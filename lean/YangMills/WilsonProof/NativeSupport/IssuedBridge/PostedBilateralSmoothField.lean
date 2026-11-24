import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedBilateralDecay
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedBilateralPositiveField
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.PostedBilateralSmoothField
open Filter Set Finset
open scoped Topology ContDiff BigOperators Classical
variable {E : ℕ → Type*} [∀ d, NormedAddCommGroup (E d)] [∀ d, NormedSpace ℝ (E d)]
variable [∀ d, CompleteSpace (E d)] (a : ∀ d, ℕ → E d)

private theorem geometric (k : ℕ) : Summable (fun n : ℕ => (n+1:ℝ)^k * (1/2:ℝ)^n) := by
  have base := summable_pow_mul_geometric_of_norm_lt_one (R:=ℝ) k (r:=1/2) (by norm_num)
  have shifted := (summable_nat_add_iff 1).2 base
  apply (shifted.mul_left 2).congr
  intro n
  change 2 * (((n+1:ℕ):ℝ)^k * (1/2:ℝ)^(n+1)) = _
  rw [Nat.cast_add_one,pow_succ]
  ring

theorem original (d : ℕ) : ContDiff ℝ ∞ (PostedBilateralPositiveField.field a d) := by
  choose C nonneg bounds using (PostedBilateralDecay.original a d)
  unfold PostedBilateralPositiveField.field
  apply contDiff_tsum_of_eventually (𝕜:=ℝ) (N:=⊤)
    (f:=fun (n:ℕ) (t:ℝ) => PostedBilateralFieldCutoff.weight a n t • a d n)
    (v:=fun (k n : ℕ) => C k * ((n+1:ℝ)^k * (1/2:ℝ)^n))
  · intro n
    exact (PostedBilateralFieldCutoff.original a n).1.smul contDiff_const
  · intro k _
    exact (geometric k).mul_left (C k)
  · intro k _
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop (max d (k+1))] with n hn t
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact bounds k n ((le_max_left ..).trans hn) ((le_max_right ..).trans hn) t
end IssuedBridge.PostedBilateralSmoothField
