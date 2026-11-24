import YM.Integration.WilsonCenteredCaptureFares
import YM.Integration.WilsonCenteredFailedHalo

/-! Charge the submitted query and each named compulsory owner separately.
Disjointness puts every unnamed absorbed owner in the original pack on
the query, even when its union with the kept supports is much longer. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredKeptOwners
open Finset RG Lattice Wilson Push.Local Function
open WilsonCenteredOriginalCaptureOwner WilsonCenteredCaptureSlots
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {ι : Type} (P : Rep G n)
    (T : ι→Support n) (I : ι→Finset ℕ)

def spare (q : Key P T I) := q.val.2 \ I q.val.1
abbrev Bins := ι ⊕ ((z : ι) × Pack P.activities (T z))

def pack (q : Key P T I) (live : (spare P T I q).Nonempty) : Pack P.activities (T q.val.1) :=
  ⟨spare P T I q,live,(fun _ hi _ hj ne=>q.property.apart (mem_sdiff.mp hi).1 (mem_sdiff.mp hj).1 ne),
    fun j hj=>(q.property.hits j (mem_sdiff.mp hj).1).resolve_left (mem_sdiff.mp hj).2⟩

def file (q : Key P T I) : Bins P T :=
  if h : (spare P T I q).Nonempty then Sum.inr ⟨q.val.1,pack P T I q h⟩ else Sum.inl q.val.1

def reopen : Bins P T → ι×Finset ℕ
  | Sum.inl z=>(z,I z)
  | Sum.inr ⟨z,C⟩=>(z,I z ∪ C.val)

lemma cover (q : Key P T I) : I q.val.1 ∪ spare P T I q=q.val.2 := by
  ext j
  change j∈I q.val.1∪(q.val.2\I q.val.1) ↔ j∈q.val.2
  simp only [mem_union,mem_sdiff]
  constructor
  · rintro (h|⟨h,-⟩);exact q.property.kept h;exact h
  intro h;by_cases inside : j∈I q.val.1
  · exact Or.inl inside
  exact Or.inr ⟨h,inside⟩

lemma recover (q : Key P T I) : reopen P T I (file P T I q)=q.val := by
  have glue:=cover P T I q
  unfold file
  split
  · exact Prod.ext rfl glue
  next h=>
    have eq := Finset.not_nonempty_iff_eq_empty.mp h
    rw [eq,union_empty] at glue
    exact Prod.ext rfl glue

def drawer : Key P T I ↪ Bins P T :=
  ⟨file P T I,fun l r E=>Subtype.ext ((recover P T I l).symm.trans ((congrArg (reopen P T I) E).trans (recover P T I r)))⟩

lemma enlarged (Z : Support n) (F : Finset ℕ)
    (hits : ∀ i∈F,∃ y∈Z,y∈Push.Local.patch P.activities i) :
    coverNumber P.p.B (ground P Z F) ≤ coverNumber P.p.B Z + ∑ i∈F,coverNumber P.p.B (Push.Local.patch P.activities i) := by
  induction F using Finset.induction_on with
  | empty=>simp [ground]
  | @insert i S outside prior=>
    obtain ⟨y,root,inPatch⟩:=hits i (mem_insert_self _ _)
    have small := prior (fun j hj=>hits j (mem_insert_of_mem hj))
    have adj := Lattice.Corona.meets_sum (mem_union_left (S.biUnion (Push.Local.patch P.activities)) root) inPatch P.p.B
    have shade : ground P Z (insert i S)=ground P Z S ∪ Push.Local.patch P.activities i := by
      ext a;simp [ground,or_comm,Push.Local.patch]
    rw [shade,sum_insert outside]
    change coverNumber P.p.B (ground P Z S ∪ Push.Local.patch P.activities i)≤_
    change coverNumber P.p.B (ground P Z S∪Push.Local.patch P.activities i) ≤ coverNumber P.p.B (ground P Z S) + coverNumber P.p.B (Push.Local.patch P.activities i) at adj
    omega

def salary (e : ι→ℝ) (z : ι) :=
  Real.exp (P.p.supportExponent * ∑ i∈I z,(coverNumber P.p.B (Push.Local.patch P.activities i):ℝ))*e z

def fee (e : ι→ℝ) (k : ℕ→ℝ) (q : Key P T I) := e q.val.1*∏ j∈spare P T I q,k j

def charge (e : ι→ℝ) (k : ℕ→ℝ) : Bins P T→ℝ :=
  Sum.elim (fun z=>P.p.mass (T z) (salary P I e z))
    (fun z=>P.p.mass (T z.1 ∪ z.2.val.biUnion (Push.Local.patch P.activities)) (salary P I e z.1*∏ i∈z.2.val,k i))

lemma affordable (q : Key P T I) (e : ι→ℝ) (k : ℕ→ℝ) (pos : ∀ i,0≤e i) (hk : ∀ i,0≤k i)
    (home : ∀ z,e z≠0→∀ i∈I z,∃ u∈T z,u∈Push.Local.patch P.activities i) :
    P.p.mass (ground P (T q.val.1) q.val.2) (fee P T I e k q) ≤ charge P T I e k (file P T I q) := by
  let z:=q.val.1
  let S:=spare P T I q
  let Y:=ground P (T z) S
  have bill : charge P T I e k (file P T I q) = P.p.mass Y (salary P I e z*∏ i∈S,k i) := by
    unfold file
    split
    · rfl
    next h=>
      have eq:S=∅:=Finset.not_nonempty_iff_eq_empty.mp h
      simp [charge,Y,ground,eq,z]
  rw [bill]
  by_cases blank : e z=0
  · change P.p.mass _ (e z*_)≤_;simp [salary,blank,BudgetPoint.mass]
  have geometry : coverNumber P.p.B (ground P Y (I z)) ≤ coverNumber P.p.B Y+∑ i∈I z,coverNumber P.p.B (Push.Local.patch P.activities i) :=
    enlarged P Y _ fun i hi=>by
      obtain ⟨u,hu,hh⟩:=home z blank i hi
      exact ⟨u,mem_union_left _ hu,hh⟩
  have eq : ground P (T z) q.val.2 = ground P Y (I z) := by
    have glued : I z∪S=q.val.2 := cover P T I q
    rw [←glued]
    ext u
    simp only [Y,ground,mem_union,mem_biUnion]
    grind
  rw [eq]
  have geo : (coverNumber P.p.B (ground P Y (I z)) : ℝ) ≤
      (coverNumber P.p.B Y : ℝ)+∑ i∈I z,(coverNumber P.p.B (Push.Local.patch P.activities i):ℝ) := by exact_mod_cast geometry
  have nonneg : 0≤∏ i∈S,k i:=prod_nonneg fun i _=>hk i
  change Real.exp (P.p.supportExponent*(coverNumber P.p.B (ground P Y (I z)):ℝ))*(e z*∏ i∈S,k i)≤_
  calc
    _ ≤ Real.exp (P.p.supportExponent*((coverNumber P.p.B Y:ℝ)+∑ i∈I z,(coverNumber P.p.B (Push.Local.patch P.activities i):ℝ)))*(e z*∏i∈S,k i) :=
      mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left geo P.p.exponent_pos.le)) (mul_nonneg (pos _) nonneg)
    _ = _ := by rw [mul_add,Real.exp_add];unfold BudgetPoint.mass salary;ring

theorem roster (e : ι→ℝ) (k : ℕ→ℝ) (pos : ∀ i,0≤e i) (hk : ∀ i,0≤k i)
    (home : ∀ z,e z≠0→∀ i∈I z,∃ u∈T z,u∈Push.Local.patch P.activities i) {a b : ℝ}
    (base : SumBudget (fun z=>P.p.mass (T z) (salary P I e z)) a)
    (next : SumBudget (fun z : (i:ι)×Pack P.activities (T i)=>P.p.mass (T z.1 ∪ z.2.val.biUnion (Push.Local.patch P.activities))
      (salary P I e z.1*∏i∈z.2.val,k i)) b) :
    SumBudget (fun q : Key P T I=>P.p.mass (ground P (T q.val.1) q.val.2) (fee P T I e k q)) (a+b) := by
  have H:=HasSum.sum (f:=charge P T I e k) base.2.1.hasSum next.2.1.hasSum
  have nn : ∀ c,0≤charge P T I e k c:=fun c=>Sum.recOn c base.1 next.1
  have small := H.summable.comp_injective (drawer P T I).injective
  have cost : SumBudget (fun q : Key P T I=>charge P T I e k (file P T I q)) (a+b) :=
    ⟨fun _=>nn _,small,(tsum_comp_le_tsum_of_inj H.summable nn (drawer P T I).injective).trans
      (H.tsum_eq.le.trans (add_le_add base.2.2 next.2.2))⟩
  exact sumBudget_mono cost (fun q=>mul_nonneg (Real.exp_pos _).le
    (mul_nonneg (pos _) (prod_nonneg (fun i _=>hk i))))
    (fun q=>affordable P T I q e k pos hk home) le_rfl

end YM.Integration.WilsonCenteredKeptOwners
