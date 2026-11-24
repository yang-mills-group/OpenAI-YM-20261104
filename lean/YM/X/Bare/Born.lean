import YM.X.Scheme.Bank
import YM.PertExtension.FreePrescription
/-!
A ladder of bare columns. **At each weight** first apply the natural RIGHT INVERSE from Wick fields onto the full Label alphabet. Not necessarily a presentation selecting a subset of letters. It keeps slot and engineering grade and signed/orthogonal and real. Lift first through that column's own grade horizon never reinitializing a later-horizon stencil. This file extends ANY matrix array across this choice, with exact hierarchy restrict; later feed lattice regulator arrays.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Bare
open Pert Pert.RawLabels Pert.Position Maxwell Maxwell.Free Labels Function Set Filter
open PertExtension PertExtension.Horizon Lattice RG Source Wilson LatticePT
open scoped Topology BigOperators Classical
variable {G : Gauge} (F:Labels.Frames G) (H:Hol G) (S:∀ n, SectionData (F.level n))(hS:∀ n,(S n).Sound H)(hP:∀ n, Bid.pop (S n))
variable {d e n : ℕ}

set_option quotPrecheck false
local notation "I" => (F.level d).Index -- quot issue
local notation "V" => LatticePT.Word G
local notation "R" => raiseLabel G
abbrev wt {d} (i:(F.level d).Index):= ((F.level d).grades i).1
def base {d}(i:(F.level d).Index): (F.level (wt F i)).Index:= (counterpart F i).choose
def grade {d} (i:(F.level d).Index):= (F.level d).grades i
lemma base_grade (i:I) : grade F (base F i)=grade F i:= (counterpart F i).choose_spec.2

-- constructors ergonomic dependent weight
local notation "Ξ" => (F.level d)
def tell (i:I)(he:wt F i=d): V:= ⟨d,_,S _,H,hS _,hP _,i,he⟩
def born {d}(i:(F.level d).Index) := tell F H S hS hP (base F i) (congr_arg Prod.fst (base_grade F i))
lemma base_raises (i:I): R ((F.level d).bound i) ((F.level (wt F i)).basis (base F i))=(F.level d).basis i:= by rw [base,(counterpart F i).choose_spec.1]; rfl

def Collar := (w:ℕ) × (F.level w).Index
def pin (i:I) : Collar F:= ⟨wt F i,base F i⟩
def valley : Collar F → Labels.Pol G:= fun x=> ((F.level x.1).basis x.2).val
lemma value (i:I) : valley F (pin F i)=((F.level d).basis i).val := congr_arg Subtype.val (base_raises F i)

lemma pin_same {i:I} {j:(F.level e).Index}(x: ((F.level d).basis i).val=((F.level e).basis j).val) : pin F i=pin F j:= by
   have h : grade F i=grade F j:= pure_unique ((F.level d).basis.ne_zero i) _ _ ((F.level d).pure i) (by rw [pure_grade,x]; exact (F.level e).pure j)
   have hw : (pin F i).1=(pin F j).1:= congr_arg Prod.fst h
   have hv: valley F (pin F i)=valley F (pin F j):= by rw [value,value];exact x
   generalize pin F i = a at *
   generalize pin F j = b at *
   rcases a with ⟨a,s⟩; rcases b with ⟨b,u⟩; dsimp only at hw; subst b; apply congr_arg (Sigma.mk (β:=fun i => (F.level i).Index) a); exact (F.level a).basis.injective (Subtype.ext hv)
lemma re_born {i:I}{j:(F.level e).Index}(x: ((F.level d).basis i).val=((F.level e).basis j).val): born F H S hS hP i=born F H S hS hP j:= by
   let m : Collar F→ Option V:= fun a=> if hj:wt F a.2=a.1 then some (tell F H S hS hP a.2 hj) else none
   have hh{d}(i:(F.level d).Index) : m (pin F i)=some (born F H S hS hP i):= dif_pos (congr_arg Prod.fst (base_grade F i))
   exact Option.some.inj ((hh i).symm.trans ((congr_arg m (pin_same F x)).trans (hh j)))

local notation "m" => born F H S hS hP

def spread {T : Type*} {I' : Type*}[AddCommMonoid T][Module ℂ T][Fintype I'](B:Module.Basis I' ℂ T)(a:(Fin n→I')→ℂ) : MultilinearMap ℂ (fun _:Fin n=> T) ℂ:=
   ∑ q:Fin n→I',(MultilinearMap.mkPiRing ℂ (Fin n) (a q)).compLinearMap (fun i=> B.coord (q i))
lemma spread_value {T : Type*} {I' : Type*}[AddCommMonoid T][Module ℂ T][Fintype I'](B:Module.Basis I' ℂ T)(a:(Fin n→I')→ℂ)(q:Fin n→T) : spread B a q=∑ p:Fin n→I',(∏ i,B.coord (p i) (q i))* a p := by simp [spread,MultilinearMap.sum_apply, smul_eq_mul]
lemma spread_eval {T : Type*} {I' : Type*}[AddCommMonoid T][Module ℂ T][Fintype I'](B:Module.Basis I' ℂ T)(a:(Fin n→I')→ℂ)(q:Fin n→ I'): spread B a (B ∘ q)=a q:= by
   rw [spread_value,Finset.sum_eq_single_of_mem q (Finset.mem_univ q)]
   · simp
   intro p hp he; obtain ⟨i,hi⟩:= not_forall.mp (mt funext he); rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi,Ne.symm hi]),zero_mul]

def offspring (d:ℕ) (a:(Fin n→ LatticePT.Word G)→ℂ) : MultilinearMap ℂ (fun _ : Fin n=> Label G d) ℂ := spread (F.level d).basis (fun p=> a (born F H S hS hP ∘ p))
lemma offspring_up (a:(Fin n→V) → ℂ) (h:d≤e) : (offspring F H S hS hP e a).compLinearMap (fun _=> raiseLabel G h)=offspring F H S hS hP d a:= by
   refine Module.Basis.ext_multilinear (e:=fun _=> (F.level d).basis) ?_; intro p
   choose w hw using fun i:Fin n=>reference_rises F h (p i)
   rw [MultilinearMap.compLinearMap_apply,show (fun i:Fin n=> R h ((F.level d).basis (p i))) =(F.level e).basis ∘ w from funext hw]
   change spread _ _ _ = spread _ _ ((F.level d).basis ∘ p); rw [spread_eval,spread_eval]; refine congr_arg a (funext (fun i=>Eq.symm (re_born F H S hS hP (congr_arg (fun q:Label G e=>q.val) (hw i)))))

/-- From the compatible grade-homogeneous right inverse. -/
def adopt (d:ℕ) (a:(Fin n→ LatticePT.Word G)→ℂ) : MultilinearMap ℂ (fun _:Fin n=> E F d) ℂ:= (offspring F H S hS hP d a).compLinearMap (fun _=> physicalLabel F d)
lemma adopt_up (a:(Fin n→V) → ℂ) (h:d≤e): (adopt F H S hS hP e a).compLinearMap (fun _=> up F h)=adopt F H S hS hP d a:= by
   ext1 p
   change offspring F H S hS hP e a _=offspring F H S hS hP d a _
   rw [← offspring_up F H S hS hP a h]; rw [MultilinearMap.compLinearMap_apply]; exact congr_arg _ (funext (fun i=> physical_inclusion F (scheme_filters F) h (p i)))
end YM.PositionX.Bare
