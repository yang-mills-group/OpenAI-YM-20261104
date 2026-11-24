import YM.Integration.FVA1Physical.Wilson.TiltStencil
import YM.MSbar.Lapaz.Scrolls

/-! Computing the normalized Wilson numerator and denominator to a higher order
preserves every earlier coefficient. The price of returning to the requested
order uses only the omitted coefficients, including at a nonzero retained field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Matrix Finset MSbar MSbar.Duel MSbar.Cacao MSbar.Bakery MSbar.Bakery.Portal
open Push.Uniform YM.Integration.FVA1Physical.Wilson
open scoped Classical BigOperators

theorem owes_prefix {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (P : Matrix ι σ ℝ) {C : Matrix σ σ ℝ} (pos : C.PosDef) (Q S : SpringK ι)
    (kind : Kind Q) (x : View ι) {p n i : ℕ} (hip : i ≤ p) (hin : i ≤ n) :
    PowerSeries.coeff i (Lapaz.owes P C Q S x n) = PowerSeries.coeff i (Lapaz.owes P C Q S x p) := by
  simp only [Lapaz.owes, picture, PowerSeries.coeff_map]
  exact (tiltedStencil_eq_grow P x pos Q S kind (n+1) i (by omega)).symm.trans
    (tiltedStencil_eq_grow P x pos Q S kind (p+1) i (by omega))

theorem price_after_truncating (a b : PowerSeries ℝ) (p d : ℕ) {t B : ℝ}
    (ht : 0 ≤ t) (h1 : t ≤ 1)
    (lower : ∀ i ≤ p, PowerSeries.coeff i a = PowerSeries.coeff i b)
    (upper : ∀ i, p < i → i ≤ p+d → |PowerSeries.coeff i a| ≤ B) :
    |taste (p+d) a t - taste p b t| ≤ (d:ℝ) * t^(p+1) * B := by
  let f := fun i : ℕ => t^i * PowerSeries.coeff i a
  have same : (∑ i∈range (p+1), f i) = taste p b t := by
    apply sum_congr rfl
    intro i hi
    exact congrArg (t^i * ·) (lower i (Nat.lt_succ_iff.mp (mem_range.mp hi)))
  have split : taste (p+d) a t = taste p b t + ∑ j∈range d, f (p+1+j) := by
    change (∑ i∈range (p+d+1), f i) = _
    rw [show p+d+1=p+1+d by omega, sum_range_add, same]
  rw [split,add_sub_cancel_left]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    (∑ j∈range d, |f (p+1+j)|) ≤ ∑ _j∈range d, t^(p+1)*B := by
      apply sum_le_sum
      intro j hj
      have hjd := mem_range.mp hj
      dsimp only [f]
      rw [abs_mul,abs_of_nonneg (pow_nonneg ht _),pow_add]
      exact mul_le_mul (mul_le_of_le_one_right (pow_nonneg ht _) (pow_le_one₀ ht h1))
        (upper _ (by omega) (by omega)) (abs_nonneg _) (pow_nonneg ht _)
    _ = (d:ℝ)*t^(p+1)*B := by simp [mul_assoc]

end YM.Integration.FVA1Physical.Round2.Curvature
