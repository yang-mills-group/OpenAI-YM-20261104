import YM.Frontier.Tuning.CauchySwitch
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville

/-!
# One-var remainders at growing radius

The perturbative grading uses an auxiliary variable with actual evaluation
at 1. Recover the factorial-normalized coefficients and last tail at that
argument, suitable for angular derivatives using the same receipt for the
angular `Box` on a slightly larger disk.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Analytic
open Filter Function Set MeasureTheory Complex Metric Topology Finset
open ConnectedActivityE6.Blaze
open scoped Topology Real ContDiff Interval

section scalar
variable {F:Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (f:ℂ→F)
def pick (n:ℕ) := (n.factorial:ℂ)⁻¹ • iteratedDeriv n f 0
def tail (p:ℕ):= f 1 - (range p).sum (pick f)
variable {C R :ℝ}

lemma pick_norm (n:ℕ)(hR:0<R)(hF:DiffContOnCl ℂ f (ball 0 R))(h : ∀ z∈sphere (0:ℂ) R, ‖f z‖≤C) :
    ‖pick f n‖≤ C*(R⁻¹)^n:= by
  have hx : 0 < (n.factorial:ℝ):= Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [pick,norm_smul,norm_inv, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left (norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hF h) (inv_nonneg.mpr hx.le)).trans
  rw [← mul_div_assoc,←mul_assoc,inv_mul_cancel₀ hx.ne',one_mul,inv_pow,div_eq_mul_inv]

variable (hR:2 ≤ R) (hF:DiffContOnCl ℂ f (ball 0 R)) (hc:0≤C) (h : ∀ z∈sphere (0:ℂ) R, ‖f z‖≤C)
include hR hF h
omit h in
lemma funded : HasSum (pick f) (f 1) := by
  have h:=hasSum_taylorSeries_on_ball hF.differentiableOn (z:=(1:ℂ)) (show (1:ℂ)∈ ball (0:ℂ) R by
    rw [mem_ball,dist_zero_right,norm_one]; linarith)
  simp only [sub_zero,one_pow,one_smul] at h; exact h

include hc
lemma tail_norm (p:ℕ): ‖tail f p‖ ≤ 2*C*(R⁻¹)^p:= by
  let r:=R⁻¹; have hr:0≤r:=by unfold r; positivity
  have ht:r≤1/2:= (inv_le_inv₀ (by positivity) zero_lt_two).mpr hR |>.trans_eq (by norm_num)
  have hp:r<1:=by linarith
  let f' (n) := pick f (n+p); let u (n:ℕ):ℝ := C*r^(n+p)
  have hu : Summable u:= (summable_nat_add_iff p).2 ((summable_geometric_of_lt_one hr hp).mul_left C)
  have hv n : ‖f' n‖ ≤ u n:= pick_norm f _ (by positivity) hF h
  have he : Summable (fun i=> ‖f' i‖):= Summable.of_nonneg_of_le (fun i=>norm_nonneg _) hv hu
  calc
    _ = ‖∑' i,f' i‖:= by
      unfold tail; rw [← (funded f hR hF).tsum_eq, ← (funded f hR hF).summable.sum_add_tsum_nat_add p,add_sub_cancel_left]
    _ ≤ ∑' i,u i:=(norm_tsum_le_tsum_norm he).trans (he.tsum_le_tsum hv hu)
    _ ≤ _:= by
      unfold u; simp_rw [pow_add,←mul_assoc,tsum_mul_right,tsum_mul_left,tsum_geometric_of_lt_one hr hp]
      have h₁:(1-r)⁻¹ ≤ 2:=by have h:1/(1-r) ≤ 2:=(div_le_iff₀ (by linarith only [hp])).mpr (by linarith only [ht]); simpa using! h
      exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left h₁ hc).trans_eq (mul_comm ..)) (pow_nonneg hr _)
end scalar
end YM.RG01.Analytic
