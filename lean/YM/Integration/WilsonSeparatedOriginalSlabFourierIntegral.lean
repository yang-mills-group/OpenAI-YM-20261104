import YM.Integration.WilsonSeparatedOriginalSlabFourierAtlas
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The common Wilson center stays inside its original signed test integral when the full angular source is reconstructed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFourierIntegral
open Function Set MeasureTheory Filter RG05Readout RG05Readout.Native RG05Readout.Pulse
open scoped BigOperators Classical Topology ContDiff

theorem purchased {V:Type*}[Countable V](c:V→ℂ)(cost:V→ℝ)(H:V→E4→ℂ)(F:E4→ℂ)(g:Body){A:ℝ}
    (fund:Summable (fun k=>‖c k‖*cost k))(continuous:∀k,Continuous (H k))(reach:∀k z,‖H k z‖≤A*cost k)
    (joined:∀z∈Native.box,HasSum (fun k=>c k*H k z) (F z)):
    HasSum (fun k=>c k*(∫z in Native.box,g.val z*H k z)) (∫z in Native.box,g.val z*F z):=by
  let μ:=volume.restrict Native.box
  let data (k:V)(z:E4):ℂ:=c k*(g.val z*H k z)
  have gc:Continuous g.val:=(show ContDiff ℝ ∞ g.val from g.property).continuous
  have gint:Integrable (fun z=>‖g.val z‖) μ:=ContinuousOn.integrableOn_compact Pert.Cellular.cells_compact gc.norm.continuousOn
  have live (k:V):Integrable (data k) μ:=ContinuousOn.integrableOn_compact Pert.Cellular.cells_compact (continuous_const.mul (gc.mul (continuous k))).continuousOn
  have major (k:V):(∫z,‖data k z‖ ∂μ)≤(‖c k‖*cost k)*(A*(∫z,‖g.val z‖ ∂μ)):=by
    calc
      _≤∫z,((‖c k‖*cost k)*A)*‖g.val z‖ ∂μ:=by
        apply integral_mono (live k).norm (gint.const_mul _)
        intro z;change ‖c k*(g.val z*H k z)‖≤_;rw [norm_mul,norm_mul]
        have spend:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (reach k z) (norm_nonneg (g.val z))) (norm_nonneg (c k))
        exact spend.trans_eq (by ring)
      _=_:=by rw [integral_const_mul];ring
  have total:Summable (fun k=>∫z,‖data k z‖ ∂μ):=(fund.mul_right _).of_nonneg_of_le (fun _=>integral_nonneg (fun _=>norm_nonneg _)) major
  have whole:=hasSum_integral_of_summable_integral_norm live total
  have eq:(fun z=>∑'k,data k z)=ᵐ[μ] fun z=>g.val z*F z:=by
    filter_upwards [ae_restrict_mem Pert.Cellular.cells_compact.measurableSet] with z hz
    have s:HasSum (fun k=>data k z) (g.val z*F z):=by simpa only [data,mul_left_comm (g.val z)] using (joined z hz).mul_left (g.val z)
    exact s.tsum_eq
  rw [integral_congr_ae eq] at whole
  simpa only [data,integral_const_mul] using whole

end YM.Integration.WilsonSeparatedOriginalSlabFourierIntegral
