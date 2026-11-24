import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionUnobservedCofactor

/-! A full-path, unbounded old exterior is clipped in its own numerical value.
Only its original second moment and the actual cap of the tested factor enter.
No cut of the gauge field, or reciprocal-vacuum moment, is used. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Set Finset MeasureTheory
open scoped Classical BigOperators
variable {Z:Type*}[MeasurableSpace Z](μ:Measure Z)[IsFiniteMeasure μ]

def walletTest (H:Z→ℂ)(K:ℝ):Z→ℂ:=({z|‖H z‖≤K}:Set Z).indicator H

omit [MeasurableSpace Z] in
theorem wallet_test_cap (H:Z→ℂ)(K:ℝ)(kp:0≤K)(z:Z):‖walletTest H K z‖≤K:=by
  by_cases e:‖H z‖≤K
  · simpa only [walletTest,Set.indicator_of_mem (show z∈{z|‖H z‖≤K} from e)] using e
  simpa only [walletTest,Set.indicator_of_notMem (show z∉{z|‖H z‖≤K} from e),norm_zero] using kp

omit [IsFiniteMeasure μ] in
theorem wallet_test_integrable (H:Z→ℂ)(hm:Measurable H)(hi:Integrable H μ)(K:ℝ):
    Integrable (walletTest H K) μ:=hi.indicator (measurableSet_le hm.norm measurable_const)

theorem wallet_test_tail (H:Z→ℂ)(hm:Measurable H)(h2:MemLp H 2 μ)(K:ℝ)(kp:0<K)
    (f:Z→ℂ)(fm:AEStronglyMeasurable f μ)(B:ℝ)(bn:0≤B)(cap:∀z,‖f z‖≤B):
    ‖(∫z,H z*f z ∂μ)-(∫z,walletTest H K z*f z ∂μ)‖≤
      (B/K)*∫z,‖H z‖^2 ∂μ:=by
  have hi:=h2.integrable (by norm_num)
  have si:=wallet_test_integrable μ H hm hi K
  have ri:Integrable (fun z=>H z*f z) μ:=by
    simpa only [mul_comm] using hi.bdd_mul fm (.of_forall cap)
  have wi:Integrable (fun z=>walletTest H K z*f z) μ:=by
    simpa only [mul_comm] using si.bdd_mul fm (.of_forall cap)
  have hs:Integrable (fun z=>‖H z‖^2) μ:=(memLp_two_iff_integrable_sq_norm h2.1).mp h2
  have bound(z):‖H z*f z-walletTest H K z*f z‖≤(B/K)*‖H z‖^2:=by
    by_cases e:‖H z‖≤K
    · rw [walletTest,Set.indicator_of_mem (show z∈{z|‖H z‖≤K} from e),sub_self,norm_zero]
      positivity
    rw [walletTest,Set.indicator_of_notMem (show z∉{z|‖H z‖≤K} from e),zero_mul,sub_zero,norm_mul]
    calc ‖H z‖*‖f z‖ ≤ ‖H z‖*B:=mul_le_mul_of_nonneg_left (cap z) (norm_nonneg _)
         _ ≤ (B/K)*‖H z‖^2:=by
           rw [div_mul_eq_mul_div,le_div_iff₀ kp]
           have t:=mul_le_mul_of_nonneg_left (le_of_not_ge e) (mul_nonneg bn (norm_nonneg (H z)))
           nlinarith only [t]
  rw [←integral_sub ri wi]
  exact (norm_integral_le_of_norm_le (hs.const_mul (B/K)) (.of_forall bound)).trans_eq (integral_const_mul ..)

end YM.Integration.FVA1Physical.Exchange.RoseCut
