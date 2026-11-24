import YM.Integration.WilsonThermometerWeakGrossCoupling

/-! Each fixed power of the genuine radial logarithm fits every preassigned
positive engineering loss on the actual positive-radius limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakLogPrice
open Set Filter Trace.Pilot
open scoped Topology Classical

theorem original (m:ℕ){A:ℝ}(pa:0<A):
    ∀ᶠr:ℝ in trail,(8+Real.log r⁻¹)^m≤2^m*r^(-A):=by
  have little:=(isLittleO_abs_log_rpow_rpow_nhdsGT_zero (m:ℝ) (neg_lt_zero.mpr pa)).bound (c:=1) zero_lt_one
  have low:=Real.tendsto_log_nhdsGT_zero.eventually_le_atBot (-8)
  filter_upwards [little,low,self_mem_nhdsWithin (a:=0)] with r hr small pos
  rw [Real.log_inv,abs_of_neg (by linarith : Real.log r<0)] at *
  rw [Real.rpow_natCast,one_mul,Real.norm_of_nonneg (pow_nonneg (by linarith) _),
      Real.norm_of_nonneg (Real.rpow_nonneg pos.le _)] at hr
  calc
    _≤(2*(-Real.log r))^m:=pow_le_pow_left₀ (by linarith) (by linarith) _
    _=2^m*(-Real.log r)^m:=mul_pow ..
    _≤_:=mul_le_mul_of_nonneg_left hr (by positivity)

end YM.Integration.WilsonThermometerWeakLogPrice
end
