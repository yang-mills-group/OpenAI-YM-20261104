import YM.Integration.FVA1Physical.Marked.ShortOwners

/-! Price the exact failed-source allocations on the union of the source and
its genuine vacuum host. The majorants are selected before the external
test, the field or the finite gas occurrence. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Finset Push.AbsoluteSums
open scoped Classical BigOperators
variable {G : Gauge} {c : Side} {Ω : Type}

private theorem incidence_budget (P : Rep G c) (S : Support c) {b : ℕ → ℝ} {κ : ℝ}
    (h : ∀ x : Site c, SumBudget
      (fun i => if x ∈ (P.activities.forced i).support then P.p.mass (P.activities.forced i).support (b i) else 0) κ) :
    SumBudget (fun i => ∑ x ∈ S, if x ∈ (P.activities.forced i).support then
      P.p.mass (P.activities.forced i).support (b i) else 0) ((S.card : ℝ)*κ) := by
  apply budget_of_sum
  · intro i
    exact sum_nonneg fun x _ => (h x).1 i
  · intro T
    rw [sum_comm]
    calc
      _ ≤ ∑ _ ∈ S, κ := sum_le_sum (fun x _ => budget_sum (h x) T)
      _ = _ := by simp

/-- The countable family of all possible owners. Its price depends on the
source support and the actual rooted vacuum K budget. It does not depend on
the period or the number of available vacuum labels. -/
theorem failed_source_budget (P : Rep G c) (S : Support c) (F : Ω → Config G c → ℝ)
    {C κ : ℝ} (hC : 0 ≤ C) (hF : ∀ u W, |F u W| ≤ C)
    (hK : P.activities.KBound P.p κ) :
    ∃ majorant : ℕ → ℝ, (∀ i, 0 ≤ majorant i) ∧
      (∀ u i U, |flagShare P S i U * P.activities.K i U * F u U| ≤ majorant i) ∧
      SumBudget (fun i => P.p.mass (S ∪ (P.activities.forced i).support) (majorant i))
        ((C*Real.exp (P.p.supportExponent*coverNumber P.p.B S))*((S.card : ℝ)*κ)) := by
  obtain ⟨b, h₁, h₂⟩ := hK
  let H := fun i => (P.activities.forced i).support
  let Q := fun i => (P.activities.forced i).inventory
  let D := fun i => if Disjoint S (Q i) then 0 else C*b i
  let t := P.p.supportExponent
  let J := C * Real.exp (t*coverNumber P.p.B S)
  have hj : 0 ≤ J := mul_nonneg hC (Real.exp_nonneg _)
  have hD (i) : 0 ≤ D i := by
    dsimp only [D]; split <;> first | exact le_rfl | exact mul_nonneg hC (h₁ i).1
  refine ⟨D, hD, ?_, ?_⟩
  · intro u i U
    dsimp only [D, Q]
    split
    next hd => simp [flagShare_support P S i hd U]
    next _ =>
      rw [abs_mul, abs_mul, abs_of_nonneg (flagShare_nonneg P S i U), mul_comm C]
      apply mul_le_mul _ (hF u U) (abs_nonneg _) (h₁ i).1
      apply (mul_le_of_le_one_left (abs_nonneg _) (flagShare_le_one P S i U)).trans
      simpa only [Real.norm_eq_abs] using (h₁ i).2 U
  · refine budget_mono (budget_scale hj (incidence_budget P S h₂))
      (fun i => mul_nonneg (Real.exp_nonneg _) (hD i)) ?_
    intro i
    change P.p.mass (S ∪ H i) (D i) ≤ J * ∑ x ∈ S, if x ∈ H i then P.p.mass (H i) (b i) else 0
    have hmass : 0 ≤ P.p.mass (H i) (b i) := mul_nonneg (Real.exp_nonneg _) (h₁ i).1
    by_cases hd : Disjoint S (Q i)
    · rw [show D i = 0 from if_pos hd, BudgetPoint.mass, mul_zero]
      exact mul_nonneg hj (sum_nonneg fun x _ => (h₂ x).1 i)
    · obtain ⟨y,hy,hQ⟩ := Finset.not_disjoint_iff.mp hd
      have hH : y ∈ H i := (P.activities.forced i).inventory_sup hQ
      have hsum : P.p.mass (H i) (b i) ≤ ∑ x ∈ S, if x ∈ H i then P.p.mass (H i) (b i) else 0 := by
        simpa only [if_pos hH] using
          (single_le_sum (f := fun x => if x ∈ H i then P.p.mass (H i) (b i) else 0)
            (fun x _ => (h₂ x).1 i) hy)
      apply le_trans _ (mul_le_mul_of_nonneg_left hsum hj)
      have hg := Corona.meets_sum hy hH P.p.B
      have he : Real.exp (t*coverNumber P.p.B (S ∪ H i)) ≤
          Real.exp (t*coverNumber P.p.B S) * Real.exp (t*coverNumber P.p.B (H i)) := by
        rw [← Real.exp_add, ← mul_add]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hg) P.p.exponent_pos.le)
      rw [show D i = C*b i from if_neg hd]
      change _ * (C*b i) ≤ J * (Real.exp (t*coverNumber P.p.B (H i))*b i)
      exact (mul_le_mul_of_nonneg_right he (mul_nonneg hC (h₁ i).1)).trans_eq (by dsimp [J]; ring)

end YM.Integration.FVA1Physical.Marked
