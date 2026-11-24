import YangMills.WilsonProof.NativeSupport.JointDatedNames
import YangMills.WilsonProof.NativeSupport.JointPrimitiveBudget
import YangMills.WilsonProof.NativeSupport.JointDatedMask

/-! Physical input and both tests on every genuine blocking bond receive
permanent names. Housing on any original prefix is bounded before a
position, period, tree or susceptibility sign is chosen. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Dated
open Finset Function Lattice Wilson RG RGComparison.Core16 Pressure Extra.Multi Packet
open scoped Classical BigOperators
variable {I:Type} [Fintype I] [DecidableEq I] {G:Gauge} {A:Levels G} {t N per j:ℕ}
abbrev Names (I:Type) (t N:ℕ) (n:Side):=I ⊕ ((Fin (N-t) × Bool) × Bond n)
def stage {n:Side} : Names I t N n → ℕ:=Sum.elim (fun _=>N-1) (fun b=>t+b.1.1.val)
def ready {n:Side} (j:ℕ):Finset (Names I t N n):=univ.filter (fun i=>j ≤ stage i)
def fresh {n:Side} (j:ℕ):Finset (Names I t N n):=univ.filter (fun i=>stage i=j)
omit [DecidableEq I] in
theorem date_separate (n:Side) : Disjoint (ready (I:=I) (t:=t) (N:=N) (n:=n) (j+1)) (fresh j):=by
  refine disjoint_left.mpr fun i a b=>?_
  have hi: j+1 ≤ stage i:=(mem_filter.mp a).2
  have lo:stage i=j:=(mem_filter.mp b).2
  omega

abbrev Sources (I:Type) (j N:ℕ) (c:Side):= {_i:I // j+1=N} ⊕ (Bool × Bond c)
local notation "F" => A.S.side N per
local notation "C" => A.S.side j per
local notation "S" => A.clock.op j per
def address (T:Slices A per) (tj:t ≤ j) (jn:j<N) : Sources I j N (A.S.side j per) → Names I t N (A.S.side N per) :=
  Sum.elim (fun i=>Sum.inl i.val) (fun p=>Sum.inr ((⟨j-t,by have _:=tj;have _:=jn;omega⟩,p.1),liftBond (traversal T jn.le) p.2))

variable (T:Slices A per) (tj:t ≤ j) (jn:j<N)

omit [Fintype I] [DecidableEq I] in
theorem address_injective : Injective (address (I:=I) T tj jn) := by
  rintro (i|⟨k,b⟩) (v|⟨l,c⟩) eq
  · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj eq))
  · cases eq
  · cases eq
  · have same:=Sum.inr.inj eq
    exact congrArg Sum.inr (Prod.ext (congrArg (fun p=>p.1.2) same) (liftBond_injective _ (congrArg Prod.snd same)))
omit [DecidableEq I] in
theorem name_fresh (i:Sources I j N C) : address T tj jn i∈fresh j := by
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  rcases i with i|b
  · change N-1=j
    have hi:=i.property
    omega
  · change t+(j-t)=j
    omega

def origin {n:Side} (loc:I → Site n) : Names I t N n → Site n := Sum.elim loc (fun p=>p.2.1)

variable (loc:I → Site (A.S.side N per))
def place (T:Slices A per) (loc:I → Site (A.S.side N per)) {k:ℕ} (h:k ≤ N) (x:Names I t N (A.S.side N per)):
    Site (A.S.side k per):=home (traversal T h) (origin loc x)
omit [Fintype I] [DecidableEq I] in
theorem previous_site (x:Names I t N F) : place T loc jn.le x=(S).ratio.parent (place T loc jn x) := by
  change home (traversal T jn.le) _=_;rw [traversal_push T jn];rfl
omit [Fintype I] [DecidableEq I] in
theorem true_home (c:Bool) (b:Bond C) : place T loc jn (address (I:=I) T tj jn (Sum.inr (c,b)))=(S).ratio.embed b.1 :=
  fine_birth T jn b

def attached (T:Slices A per) (tj:t ≤ j) (jn:j<N) (id:Names I t N (A.S.side N per)) : Finset (Bond (A.S.side j per)) :=
  univ.filter (fun b=>∃ k:Bool,id=address T tj jn (Sum.inr (k,b)))
omit [Fintype I] in
theorem attached_here (k:Bool) (b:Bond C) :
    attached T tj jn (address (I:=I) T tj jn (Sum.inr (k,b)))={b} := by
  ext c
  simp only [attached,mem_filter,mem_univ,true_and,mem_singleton]
  constructor
  · rintro ⟨q,same⟩; exact (congrArg Prod.snd (Sum.inr.inj (address_injective T tj jn same))).symm
  · rintro rfl;exact ⟨k,rfl⟩
theorem attached_before (v:Names I t N F) (old:v∉fresh j):attached T tj jn v=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro b hit
  obtain ⟨k,rfl⟩:=(mem_filter.mp hit).2
  exact old (name_fresh T tj jn (Sum.inr (k,b)))
omit [Fintype I] in
theorem attached_root (v:Names I t N F) (b:Bond C) (hit:b∈attached T tj jn v) :
    place T loc jn v=(S).ratio.embed b.1 := by
  obtain ⟨k,rfl⟩:=(mem_filter.mp hit).2
  exact true_home .. 

omit [DecidableEq I] in
theorem occupancy {k:ℕ} (tk:t ≤ k) (kn:k ≤ N) :
    Occupancy (place (t:=t) T loc kn ∘ (Prod.fst : Painted.Ink (Names I t N F) → Names I t N F))
      (fullMultiplicity (Fintype.card I) (N-t) (scale (traversal T (tk.trans kn)))) := by
  have quota:=dated_occupancy (J:=Fin (N-t) × Bool) (traversal T kn) loc
  have grow:=prefix_monotone T tk kn
  intro x
  apply (quota x).trans
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,fullMultiplicity]
  rw [Nat.mul_comm (N-t) 2]
  gcongr

end YM.Integration.InletSusceptibility.Dated
