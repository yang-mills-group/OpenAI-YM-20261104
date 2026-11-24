import Mathlib.Analysis.PSeries
import YM.Next.SCHEDULE.Continuing
import YM.Extra.ITERATION_NO_LOSS.Sums

/-! A width bound for the whole physical length distribution. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FundedCloverWidthMoment
open Filter Finset Extra.Iteration Next.Scheduling
open scoped Classical BigOperators Topology

def square (n:ℕ):ℝ:=(((n:ℝ)+1)^2)⁻¹

theorem squares : Summable square := by
  have h:=(summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr (by norm_num : (-2:ℝ)< -1))
  refine h.congr ?_
  intro n
  simp only [square,Nat.cast_add,Nat.cast_one,Real.rpow_neg (by positivity : 0≤(n:ℝ)+1),Real.rpow_two]

def coefficient (d:ℕ):ℝ:=Real.exp 1*(d+2).factorial*(4:ℝ)^(d+2)*(∑' n,square n)

theorem coefficient_nonneg (d:ℕ) : 0≤coefficient d := by
  unfold coefficient
  exact mul_nonneg (by positivity) (tsum_nonneg fun n=>by unfold square;positivity)

private theorem term (d:ℕ) (x:ℝ) (hx:0<x) (n:ℕ) :
    decay d x n≤ momentPrice (d+2) x*square n := by
  have a:=spendMoment (d+2) (z:=(n:ℝ)) hx (Nat.cast_nonneg n)
  rw [add_comm (1:ℝ) (n:ℝ)] at a
  unfold square
  rw [←div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0<((n:ℝ)+1)^2)).mpr
  calc _ = ((n:ℝ)+1)^(d+2)*Real.exp (-(x*n)):=by unfold decay;rw [pow_add];ring_nf
    _ ≤ (momentPrice (d+2) x*Real.exp (x*n))*Real.exp (-(x*n)):=
      mul_le_mul_of_nonneg_right a (Real.exp_nonneg _)
    _ = momentPrice (d+2) x:=by rw [mul_assoc,←Real.exp_add];simp

theorem price (d:ℕ) {σ:ℝ} (hs:0<σ) (hu:σ≤1) :
    momentCost d σ≤coefficient d*(σ⁻¹)^(d+2) := by
  have pos:0<σ/4:=by positivity
  have zeta:0≤ ∑' n,square n:=tsum_nonneg fun n=>by unfold square;positivity
  have scalar:momentPrice (d+2) (σ/4)≤Real.exp 1*(d+2).factorial*(4*σ⁻¹)^(d+2):=by
    unfold momentPrice
    rw [div_eq_mul_inv,←inv_pow,inv_div,div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_monotone (by linarith))
      (by positivity)) (by positivity)
  calc momentCost d σ ≤ ∑' n,momentPrice (d+2) (σ/4)*square n:=
      (decay_summable d _ pos).tsum_le_tsum (term d _ pos) (squares.mul_left _)
    _ = momentPrice (d+2) (σ/4)*(∑' n,square n):=tsum_mul_left
    _ ≤ (Real.exp 1*(d+2).factorial*(4*σ⁻¹)^(d+2))*(∑' n,square n):=
      mul_le_mul_of_nonneg_right scalar zeta
    _ = coefficient d*(σ⁻¹)^(d+2):=by unfold coefficient;rw [mul_pow];ring

end YM.Integration.FundedCloverWidthMoment
end
