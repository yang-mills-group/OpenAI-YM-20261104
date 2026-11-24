import YM.Integration.WilsonCenteredCaptureSlots
import YM.Integration.WilsonCenteredCaptureOwnerTariff

/-! Price the actual filed entries. Each old marked owner contributes
once. Its optional quiet partners use only the one local vacuum tariff. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCaptureFares
open Finset Function Lattice RG Wilson Push.Local Planned.GuardedAtom
open WilsonCenteredCaptureSlots WilsonCenteredOriginalCaptureOwner
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {ι : Type} (P : Rep G n)
  (T : ι × ℕ → Support n)

abbrev Sel (z : ι × ℕ) : Finset ℕ := {z.2}
abbrev Tab := Key P T Sel
abbrev Alternatives := (ι × ℕ) ⊕ ((z : ι × ℕ) × Pack P.activities (T z))
def extra (q : Tab P T) := q.val.2 \ Sel q.val.1

def pack (q : Tab P T) (live : (extra P T q).Nonempty) : Pack P.activities (T q.val.1) :=
  ⟨extra P T q,live,(fun _ hi _ hj ne=>q.property.apart (mem_sdiff.mp hi).1 (mem_sdiff.mp hj).1 ne),by
    intro j hj
    obtain ⟨old,other⟩ := mem_sdiff.mp hj
    exact (q.property.hits j old).resolve_left other⟩

def route (q : Tab P T) : Alternatives P T :=
  if h : (extra P T q).Nonempty then Sum.inr ⟨q.val.1,pack P T q h⟩ else Sum.inl q.val.1

def reopen : Alternatives P T → (ι × ℕ) × Finset ℕ
  | Sum.inl z => (z,{z.2})
  | Sum.inr ⟨z,C⟩ => (z,insert z.2 C.val)

theorem recovered (q : Tab P T) : reopen P T (route P T q) = q.val := by
  have own := q.property.kept (Finset.mem_singleton_self q.val.1.2)
  have cover : insert q.val.1.2 (extra P T q) = q.val.2 := by
    unfold extra Sel
    ext j
    simp only [mem_insert,mem_sdiff,mem_singleton]
    constructor
    · rintro (rfl|⟨hj,_⟩)
      · exact own
      · exact hj
    intro hj
    by_cases eq : j=q.val.1.2
    · exact Or.inl eq
    · exact Or.inr ⟨hj,eq⟩
  unfold route
  split
  · exact Prod.ext rfl cover
  next h =>
    have blank := Finset.not_nonempty_iff_eq_empty.mp h
    rw [blank,Finset.insert_empty] at cover
    exact Prod.ext rfl cover

def booking : Tab P T ↪ Alternatives P T :=
  ⟨route P T,fun a b e=>Subtype.ext ((recovered P T a).symm.trans ((congrArg (reopen P T) e).trans (recovered P T b)))⟩

def fee (e : ι × ℕ → ℝ) (k : ℕ → ℝ) (q : Tab P T) :=
  e q.val.1 * ∏ j ∈ extra P T q, k j

def charge (e : ι × ℕ → ℝ) (k : ℕ → ℝ) : Alternatives P T → ℝ :=
  Sum.elim (fun z=>P.p.mass (T z) (e z)) (fun s=>P.p.mass (T s.1 ∪ s.2.val.biUnion (Push.Local.patch P.activities))
    (e s.1 * ∏ j∈s.2.val,k j))

theorem same (q : Tab P T) (home : ∀ z, (P.activities.forced z.2).support ⊆ T z)
    (e : ι × ℕ → ℝ) (k : ℕ → ℝ) :
    P.p.mass (ground P (T q.val.1) q.val.2) (fee P T e k q) =
      charge P T e k (route P T q) := by
  have dom : ground P (T q.val.1) q.val.2 = T q.val.1 ∪ (extra P T q).biUnion (Push.Local.patch P.activities) := by
    ext y
    constructor
    · intro hy
      rcases mem_union.mp hy with here|owners
      · exact mem_union_left _ here
      obtain ⟨j,hj,h⟩ := mem_biUnion.mp owners
      by_cases eq : j=q.val.1.2
      · exact mem_union_left _ (home q.val.1 (eq ▸ h))
      · exact mem_union_right _ (mem_biUnion.mpr ⟨j,mem_sdiff.mpr ⟨hj,fun hin=>eq (mem_singleton.mp hin)⟩,h⟩)
    · intro hy
      rcases mem_union.mp hy with here|outs
      · exact mem_union_left _ here
      obtain ⟨j,hj,h⟩ := mem_biUnion.mp outs
      exact mem_union_right _ (mem_biUnion.mpr ⟨j,(mem_sdiff.mp hj).1,h⟩)
  rw [dom]
  unfold route
  split
  · rfl
  next h =>
    have blank := Finset.not_nonempty_iff_eq_empty.mp h
    simp [fee,blank,charge]

theorem roster (home : ∀ z, (P.activities.forced z.2).support ⊆ T z) (e : ι × ℕ → ℝ) (k : ℕ → ℝ)
    {a b : ℝ} (bare : SumBudget (fun z=>P.p.mass (T z) (e z)) a)
    (companions : SumBudget (fun s : (z : ι × ℕ) × Pack P.activities (T z) =>
      P.p.mass (T s.1 ∪ s.2.val.biUnion (Push.Local.patch P.activities)) (e s.1 * ∏ j∈s.2.val,k j)) b) :
    SumBudget (fun q : Tab P T => P.p.mass (ground P (T q.val.1) q.val.2) (fee P T e k q)) (a+b) := by
  have hp : HasSum (charge P T e k) ((∑' z,P.p.mass (T z) (e z)) + (∑' s : (z : ι × ℕ) × Pack P.activities (T z),
      P.p.mass (T s.1 ∪ s.2.val.biUnion (Push.Local.patch P.activities)) (e s.1 * ∏ j∈s.2.val,k j))) :=
    HasSum.sum (f:=charge P T e k) bare.2.1.hasSum companions.2.1.hasSum
  have pos : ∀ i, 0 ≤ charge P T e k i := fun i=>Sum.recOn i bare.1 companions.1
  simp_rw [same P T _ home e k]
  exact ⟨fun q=>pos _, hp.summable.comp_injective (booking P T).injective,
    (tsum_comp_le_tsum_of_inj hp.summable pos (booking P T).injective).trans (hp.tsum_eq.le.trans (add_le_add bare.2.2 companions.2.2))⟩

end YM.Integration.WilsonCenteredCaptureFares
