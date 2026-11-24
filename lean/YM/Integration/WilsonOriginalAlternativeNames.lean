import YM.RG05Readout.Many.Consider
import YM.RG02.Marker.Restriction

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeNames
open Function Finset Marker RG05Readout.Many Extra.Trajectories
open scoped Classical BigOperators
variable {V : Type} [DecidableEq V] [Fintype V] (R : Census V)

abbrev Port := Fin 3
abbrev board := Lift R (Prod.fst : V × Port → V)

theorem legal (s : (board R).Mode) : Lit R Prod.fst s.val :=
  (Finset.mem_filter.mp s.property).2

def base (s : (board R).Mode) : R.Mode := (legal R s).climb

def pin (c : V → Port) : V ↪ V × Port := ⟨fun v=>(v,c v),fun _ _ h=>congrArg Prod.fst h⟩

def names (c : V → Port) : Names R (board R) where
  e := pin c
  visible s := by
    refine (chamber R Prod.fst) _ ⟨?_,?_⟩
    · simp [Finset.image_image,pin,Function.comp_def]
    intro u hu v hv eq
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hv
    exact congrArg (pin c) eq

def read (c : V → Port) : Poly (board R) →ₐ[ℂ] Poly R := RG02.Grade.restrict (names R c)

theorem read_part (c : V → Port) (a : Poly (board R)) (s : R.Mode) :
    (read R c a).part s = a.part ((names R c).share s) := rfl

theorem base_named (c : V → Port) (s : R.Mode) : base R ((names R c).share s)=s := by
  apply Subtype.ext
  change (s.val.image (pin c)).image Prod.fst=s.val
  simp [Finset.image_image,pin,Function.comp_def]

def select (s : (board R).Mode) (i:V) : Port :=
  if h : ∃j:Port,(i,j)∈s.val then h.choose else 0

theorem selected (s : (board R).Mode) {i : V} {j : Port} (h : (i,j)∈s.val) :
    select R s i = j := by
  let e : ∃k:Port,(i,k)∈s.val := ⟨j,h⟩
  rw [select,dif_pos e]
  exact congrArg Prod.snd ((legal R s).2 e.choose_spec h rfl)

theorem covered (s : (board R).Mode) : (names R (select R s)).share (base R s)=s := by
  apply Subtype.ext
  change (s.val.image Prod.fst).image (pin (select R s))=s.val
  ext x
  constructor
  · rintro hx
    obtain ⟨_,hv,rfl⟩:= Finset.mem_image.mp hx
    obtain ⟨⟨v,j⟩,hj,rfl⟩ := Finset.mem_image.mp hv
    simpa [pin,selected R s hj] using hj
  · rcases x with ⟨v,j⟩
    intro h
    exact Finset.mem_image.mpr ⟨v,Finset.mem_image.mpr ⟨(v,j),h,rfl⟩,Prod.ext rfl (selected R s h)⟩

theorem joint {a b : Poly (board R)} (h : ∀c:V → Port, read R c a=read R c b) : a=b := by
  ext s
  have e:=congrArg (fun p:Poly R=>p.part (base R s)) (h (select R s))
  simpa only [read_part,covered] using e

def spread : Poly R →ₗ[ℂ] Poly (board R) where
  toFun a:=Poly.inject fun s=>a.part (base R s)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

theorem on_sheet (c : V → Port) (p : Poly R) : read R c (spread R p)=p := by
  ext s
  change p.part (base R ((names R c).share s))=p.part s
  rw [base_named]

def copies : Poly R →ₐ[ℂ] Poly (board R) :=
  AlgHom.ofLinearMap (spread R) (joint R (fun _=>by rw [on_sheet,map_one]))
    (fun _ _=>joint R (fun _=>by rw [on_sheet,map_mul,on_sheet,on_sheet]))

def retain (j : Port) : ℂ := if j=1 then 0 else 1

def inheritAll : Poly R →ₐ[ℂ] Poly (board R) :=
  (Multi.dilation (board R) (fun j=>retain j.2)).comp (copies R)

theorem inherited (p : Poly R) (s : (board R).Mode) :
    (inheritAll R p).part s=(∏ j∈s.val,retain j.2)*p.part (base R s) :=
  Multi.dilation_part .. 

theorem elected (c : V → Port) (p : Poly R) :
    read R c (inheritAll R p)=Multi.dilation R (fun v=>retain (c v)) p := by
  ext s
  rw [read_part,inherited,Multi.dilation_part,base_named]
  change (∏ j∈s.val.image (pin c),retain j.2)*_=_
  rw [Finset.prod_image (pin c).injective.injOn]
  rfl

end YM.Integration.WilsonOriginalAlternativeNames
