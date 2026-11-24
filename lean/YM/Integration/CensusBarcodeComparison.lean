import YM.Integration.AddressedCensusCharges

/-! Compare the actual signed hard functions at common physical barcodes,
including tested subfamilies on the original torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CensusBarcodeComparison

open Lattice Wilson RG MergeProof Push.AbsoluteSums
open scoped Classical BigOperators

variable {G : Gauge} {n : Side}

def native (A : Activities G n) (z : Config G n) (a : Box n) : ℂ :=
  profile A (fun i => Complex.ofReal ∘ A.K i) a z

def charge (p : BudgetPoint) (o : Site n) (a : Box n) (c : ℝ) : ℝ :=
  if o ∈ a.1 then p.mass a.1 c else 0

/-- The actual original majorants work at a smaller support exponent
without changing the grid, addresses, functions or eligibility tests. -/
theorem restrict (A : Activities G n) (p q : BudgetPoint)
    (hB : q.B = p.B) (hσ : q.supportExponent ≤ p.supportExponent)
    {γ : ℝ} (h : A.KBound p γ) : A.KBound q γ := by
  obtain ⟨u,hu,hb⟩ := h
  refine ⟨u,hu,fun o => budget_mono (hb o) ?_ ?_⟩
  · intro i
    split
    next => exact mul_nonneg (Real.exp_nonneg _) (hu i).1
    next => exact le_rfl
  · intro i
    by_cases hi : o ∈ (A.forced i).support
    · simp only [if_pos hi,BudgetPoint.mass,hB]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hσ (Nat.cast_nonneg _))) (hu i).1
    · simp only [if_neg hi,le_refl]

theorem difference (Y Z : Activities G n) (q : BudgetPoint) {y t : ℝ}
    (hy : Y.KBound q y) (hz : Z.KBound q t) (o : Site n) (z : Config G n) :
    SumBudget (fun a : Box n => charge q o a ‖native Y z a - native Z z a‖) (y+t) := by
  let rv (X : Activities G n) a := charge q o a ‖native X z a‖
  have hY : SumBudget (rv Y) y := AddressedCensusCharges.forced Y q hy o z
  have hZ : SumBudget (rv Z) t := AddressedCensusCharges.forced Z q hz o z
  have hs : SumBudget (fun a => rv Y a + rv Z a) (y+t) :=
    ⟨fun a => add_nonneg (hY.1 a) (hZ.1 a),hY.2.1.add hZ.2.1,
      (hY.2.1.tsum_add hZ.2.1).le.trans (add_le_add hY.2.2 hZ.2.2)⟩
  refine budget_mono hs ?_ ?_
  · intro a
    unfold charge;split
    next => exact mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)
    next => exact le_rfl
  · intro a
    by_cases h : o ∈ a.1
    · simp only [rv,charge,if_pos h,BudgetPoint.mass,← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.exp_nonneg _)
    · simp only [rv,charge,if_neg h,add_zero,le_refl]

/-- Test the signed barcode error with any bounded stem. All factors are
charged at each common support and its exact marked inventory. -/
theorem tested (Y Z : Activities G n) (q : BudgetPoint) {y t κ b : ℝ}
    (hy : Y.KBound q y) (hz : Z.KBound q t) (hκ : 0 < κ) (hb : 0 ≤ b)
    (o : Site n) (z : Config G n) (stem : Box n → ℂ)
    (hstem : ∀ a, ‖stem a‖ ≤ b) :
    SumBudget (fun a : Box n => charge q o a
      ‖(native Y z a-native Z z a)*stem a/(κ:ℂ)‖) ((y+t)/κ*b) := by
  let f (a : Box n) := charge q o a ‖native Y z a-native Z z a‖
  have h : SumBudget f (y+t) := difference Y Z q hy hz o z
  have hc : 0 ≤ b/κ := div_nonneg hb hκ.le
  have hs : SumBudget (fun a => (b/κ)*f a) ((y+t)/κ*b) := by
    refine ⟨fun a => mul_nonneg hc (h.1 a),h.2.1.mul_left _,?_⟩
    rw [tsum_mul_left]
    exact (mul_le_mul_of_nonneg_left h.2.2 hc).trans_eq (by ring)
  refine budget_mono hs ?_ ?_
  · intro a
    unfold charge;split
    next => exact mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)
    next => exact le_rfl
  · intro a
    by_cases ha : o ∈ a.1
    · simp only [f,charge,if_pos ha,BudgetPoint.mass,norm_div,norm_mul,Complex.norm_real,
        Real.norm_of_nonneg hκ.le]
      calc
        _ ≤ Real.exp (q.supportExponent*coverNumber q.B a.1) *
            (‖native Y z a-native Z z a‖*b/κ) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hstem a) (norm_nonneg _)) hκ.le) (Real.exp_nonneg _)
        _ = _ := by ring
    · simp only [f,charge,if_neg ha,mul_zero,le_refl]

end YM.Integration.CensusBarcodeComparison
end
