import YM.Integration.WilsonOriginalDepositedRegularWindow

/-! Hear the actual smooth complementary row with the full correlated physical cofactor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalDepositedRegularHearing
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Push.AbsoluteSums
open WilsonOriginalDepositedRegularWindow
open scoped Topology Classical BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}
  (P : Rep G n) (q : Coefficient F n) (D : ℕ)

def rejected (i : ℕ) (U : Config G n) : ℂ := if small P q D i then 0 else q.maskedTerm P i U
def tail (U : Config G n) : ℂ := ∑' i, rejected P q D i U
def fee (B : ℝ) : ℝ := Real.exp (-P.p.supportExponent*D)*B

theorem bound {o : Site n} {κ B : ℝ} (receipt : q.remBound o P κ B) (U : Config G n) :
    SumBudget (fun i=> ‖rejected P q D i U‖) (fee P D B) := by
  obtain ⟨a,b,ha,hb,total,_,⟨e,invoice,cost⟩,_⟩ := receipt
  let c := Real.exp (-P.p.supportExponent*D)
  have pos : 0 ≤ c := Real.exp_nonneg _
  apply budget_loosen (budget_mono (budget_scale pos invoice) (fun i => norm_nonneg _) ?_)
    (mul_le_mul_of_nonneg_left (show a≤B by linarith) pos)
  intro i
  by_cases near : small P q D i
  · simp only [rejected,if_pos near,norm_zero]
    exact mul_nonneg pos (mul_nonneg (Real.exp_nonneg _) (cost i).1)
  have ebound : ‖q.maskedTerm P i U‖ ≤ e i := by
    unfold Coefficient.maskedTerm
    by_cases h : Healthy P.p.threshold (q.support i) U
    · rw [masked_eq _ _ _ _ h]
      exact (cost i).2 U h [] (Nat.zero_le _) (by simp)
    · rw [masked_ne _ _ _ _ h,norm_zero]
      exact (cost i).1
  rw [rejected,if_neg near]
  apply ebound.trans
  have h : (D:ℝ) ≤ (coverNumber P.p.B (q.support i):ℝ) := by
    exact_mod_cast Nat.le_of_lt (lt_of_not_ge near)
  have ex : 1 ≤ c * Real.exp (P.p.supportExponent*coverNumber P.p.B (q.support i)) := by
    dsimp only [c]
    rw [←Real.exp_add,Real.one_le_exp_iff]
    nlinarith [mul_nonneg P.p.exponent_pos.le (sub_nonneg.mpr h)]
  exact (le_mul_of_one_le_left (cost i).1 ex).trans_eq (mul_assoc _ _ _)

theorem price {o : Site n} {κ B : ℝ} (receipt : q.remBound o P κ B) (U : Config G n) :
    ‖tail P q D U‖ ≤ fee P D B := by
  have book := bound P q D receipt U
  exact (norm_tsum_le_tsum_norm book.2.1).trans book.2.2

theorem measurable {o : Site n} {A : Hol G} (law : q.Format o A P) : Measurable (tail P q D) := by
  apply Measurable.tsum
  intro i
  change Measurable (fun U : Config G n => if small P q D i then (0:ℂ) else q.maskedTerm P i U)
  by_cases h : small P q D i
  · simp only [if_pos h]
    exact measurable_const
  · simp only [if_neg h]
    exact masked_measurable P.p.threshold (q.support i) (q.regular i) (law.smooth i).borel

theorem heard {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {X : Ω → Config G n}
    (hx : Measurable X) (H : Ω → ℂ) (integral : Integrable H μ) {o : Site n} {κ B : ℝ}
    {A : Hol G} (law : q.Format o A P) (receipt : q.remBound o P κ B) :
    ‖∫ z, H z * tail P q D (X z) ∂μ‖ ≤ fee P D B * ∫ z, ‖H z‖ ∂μ := by
  let c := fee P D B
  have limit (z : Ω) : ‖H z * tail P q D (X z)‖ ≤ c*‖H z‖ := by
    rw [norm_mul,mul_comm c]
    exact mul_le_mul_of_nonneg_left (price P q D receipt _) (norm_nonneg _)
  have major := integral.norm.const_mul c
  have pay := major.mono' (integral.aestronglyMeasurable.mul ((measurable P q D law).comp hx).aestronglyMeasurable)
      (Filter.Eventually.of_forall limit)
  calc _ ≤ ∫ z, ‖H z * tail P q D (X z)‖ ∂μ := norm_integral_le_integral_norm _
       _ ≤ ∫ z, c*‖H z‖ ∂μ := integral_mono pay.norm major limit
       _ = _ := integral_const_mul _ _

end YM.Integration.WilsonOriginalDepositedRegularHearing
