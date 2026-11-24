import YM.Integration.WilsonThermometerWardLiveSlot

/-! Reassemble the paid regular and analytic rows at the original incoming addresses. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerFiniteModeIncome
open Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn Push.AbsoluteSums
open WilsonPrecontactSeparatedLamps
open scoped Classical BigOperators
variable {V ι T K : Type} [DecidableEq V] [Fintype K]
    {G : Gauge} {n : Side} {p : BudgetPoint} {o : V → Site n} {R : Census V}

theorem invoice (group : ι → K) (f : ι → ℝ) (price : K → ℝ)
    (income : ∀ k, SumBudget (fun i : {j // group j = k} => f i.val) (price k)) :
    SumBudget f (∑ k, price k) := by
  classical
  let entry (k : K) (i : ι) := if group i = k then f i else 0
  let mass (k : K) := ∑' i : {j // group j = k}, f i.val
  have issued (k : K) : HasSum (entry k) (mass k) := by
    have resident : Function.support (entry k) ⊆ {j | group j = k} := by
      intro j hj
      by_contra h
      exact hj (if_neg h)
    apply (hasSum_subtype_iff_of_support_subset resident).mp
    exact ((income k).2.1.hasSum.congr_fun fun i => by simp [entry, i.property])
  have total : HasSum f (∑ k, mass k) := by
    convert (hasSum_sum (s := univ) (fun k _ => issued k)) using 1
    ext i
    simp [entry]
  exact ⟨fun i => (income (group i)).1 ⟨i, rfl⟩, total.summable,
    total.tsum_eq.le.trans (Finset.sum_le_sum fun k _ => (income k).2.2)⟩

/-- A derivative envelope is selected from the wallet of the actual row's class. -/
theorem regular (L : Lamps T ι G p o R) (group : ι → K) {w : V → ℝ} {B : ℕ} {a : ℝ}
    (price : K → ℝ)
    (income : ∀ k, (portion L {j | group j = k}).Paid w B a (price k)) :
    L.Paid w B a (∑ k, price k) := by
  classical
  choose row nonneg derivative rooted using fun k => (income k).budget
  let fee (i : ι) := row (group i) ⟨i, rfl⟩
  refine ⟨fee, fun i => nonneg _ ⟨i, rfl⟩, fun i => derivative _ ⟨i, rfl⟩, ?_⟩
  intro root
  apply invoice group _ price
  intro k
  convert rooted k root using 1
  · rfl
  · apply heq_of_eq
    funext i
    obtain ⟨i, hi⟩ := i
    change group i = k at hi
    subst k
    rfl

/-- The salary is summed before tests at its elected center, on the same row model. -/
theorem offers {P : Passport n V} (X : ι → Row P R G T) (group : ι → K)
    {w : V → ℝ} {s : ℝ} (price : K → ℝ)
    (income : ∀ k, Offers (fun i : {j // group j = k} => X i.val) w s (price k)) :
    Offers X w s (∑ k, price k) := by
  intro root
  exact invoice group _ price (fun k => income k root)

end YM.Integration.WilsonThermometerFiniteModeIncome
