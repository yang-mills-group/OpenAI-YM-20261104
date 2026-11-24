import YM.Integration.WilsonPhysicalHistoryRetainedSpringSite

/-! The deposited exponential length allowance pays the true repeated
ordered path visits at any finite Taylor order. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Lattice RG Wilson
open scoped Classical BigOperators
variable {G : Gauge} {k : ℕ}

theorem length_taylor (a : Atom G k) {σ A : ℝ} (hs : 0<σ) (ha : 0≤A) (q : ℕ) (t : ℝ) :
    a.magnitude*((2*(a.length:ℝ)*A)^(q+1)*|t|^(q+1)/(q+1).factorial)≤
      a.budget σ*(2*A*|t|/σ)^(q+1) := by
  have base : 2*(a.length:ℝ)*A*|t|=(σ*a.length)*(2*A*|t|/σ) := by
    field_simp [hs.ne']
  have move : (2*(a.length:ℝ)*A)^(q+1)*|t|^(q+1)/(q+1).factorial =
      ((σ*a.length)^(q+1)/(q+1).factorial)*(2*A*|t|/σ)^(q+1) := by
    rw [←mul_pow,base,mul_pow]; ring
  rw [move,←mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.pow_div_factorial_le_exp (σ*a.length) (by positivity) (q+1)) (Finset.sum_nonneg fun _ _=>abs_nonneg _))
    (by positivity)

end YM.Integration.OriginalMarkedRunAction
