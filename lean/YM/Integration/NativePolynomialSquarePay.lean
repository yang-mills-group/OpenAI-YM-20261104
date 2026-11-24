import YM.Push.STATIONARY_UNIFORM.ScoreBounds
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! # An explicit polynomial price for the native quadratic color score

The full jet, including order zero, is bounded using the native bilinear
calculus and the actual real inner product.  The constant is fixed before the
radius and does not depend on a period or a trajectory.  The final theorem
supplies the original SquarePay record with a literal quadratic polynomial
in its original radius C * rootsCost.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativePolynomialSquarePay

open Push.Uniform
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

/-- The native unnormalised derivatives of the quadratic score through any
fixed order have an explicit quadratic bound, also on a trivial space. -/
theorem quadratic_allows {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {v : E} (hv : ‖v‖ ≤ R) :
    Allows n (fun x : E => ‖x‖ ^ 2 / 2) v
      (((2 : ℝ) ^ n / 2) * (1 + R) ^ 2) := by
  have hI : Allows n (fun x : E => x) v (1 + R) := by
    exact
      (allows_linear (n := n) (x := v) (L := ContinuousLinearMap.id ℝ E)
        (ContinuousLinearMap.norm_id_le.trans (by linarith))
        (show ‖(ContinuousLinearMap.id ℝ E) v‖ ≤ 1 + R by
          change ‖v‖ ≤ 1 + R
          linarith))
  have hQ := Allows.bilinear (innerSL ℝ (E := E)) hI hI
    (norm_innerSL_le ℝ)
  have hHalf := hQ.smul ((1 : ℝ) / 2)
  have hfun :
      (fun x : E => ((1 : ℝ) / 2) • innerSL ℝ x x) =
        (fun x : E => ‖x‖ ^ 2 / 2) := by
    funext x
    change ((1 : ℝ) / 2) * ⟪x, x⟫_ℝ = ‖x‖ ^ 2 / 2
    rw [real_inner_self_eq_norm_sq]
    ring
  have hcost :
      |(1 : ℝ) / 2| * ((2 : ℝ) ^ n * 1 * (1 + R) * (1 + R)) =
        ((2 : ℝ) ^ n / 2) * (1 + R) ^ 2 := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  rw [hfun, hcost] at hHalf
  exact hHalf

/-- The fixed constant can be chosen explicitly as 2^n/2 before every
nonnegative radius and every vector of the actual color space. -/
theorem uniform_cost (G : Gauge) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 0 ≤ R → ∀ v : G.Color, ‖v‖ ≤ R →
      Allows n (fun x : G.Color => ‖x‖ ^ 2 / 2) v (K * (1 + R) ^ 2) := by
  exact ⟨(2 : ℝ) ^ n / 2, by positivity,
    fun _ hR _ hv => quadratic_allows n hR hv⟩

/-- A direct original SquarePay receipt.  Its price is positive for all real
input parameters.  Any vector in the requested ball itself certifies that
the original radius is nonnegative, so no extra sign premise is needed. -/
theorem native_square_pay (G : Gauge) (n : ℕ) (Z μ C : ℝ) :
    SquarePay G n Z μ C
      ((2 : ℝ) ^ n * (1 + (C * rootsCost G Z μ n) ^ 2)) := by
  refine ⟨by positivity, ?_⟩
  intro v hv
  have hR : 0 ≤ C * rootsCost G Z μ n := (norm_nonneg v).trans hv
  apply (quadratic_allows n hR hv).mono
  nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
    (sq_nonneg (C * rootsCost G Z μ n - 1))]

end YM.Integration.NativePolynomialSquarePay
