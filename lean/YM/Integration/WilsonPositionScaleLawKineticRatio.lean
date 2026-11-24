import YM.Integration.WilsonPositionScaleLawClock
import YM.Integration.WilsonPositionScaleLawCompactNative

/-! The original measured one-loop kinetic law already pays the first signed
coupling scale comparison, uniformly on every positive compact ratio window. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawKineticRatio
open Function Filter Set Asymptotics Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawCompactNative (positive bothHomes)
open scoped Topology Classical Asymptotics
variable [W:RangeSpec]

theorem geometry:Tendsto (fun z:ℝ×Ratio=>LogV (z.2.val*z.1)/LogV z.1) sweep (𝓝 1):=by
  let u(z:ℝ×Ratio):= -Real.log z.2.val
  have large:Tendsto (fun z:ℝ×Ratio=>LogV z.1) sweep atTop:=PhysMS.to_log_zoom.comp tendsto_fst
  have live:∀ᶠz:ℝ×Ratio in sweep,0<z.1:=tendsto_fst.eventually self_mem_nhdsWithin
  have nonneg(z:ℝ×Ratio):0≤u z:=neg_nonneg.mpr (Real.log_nonpos (positive z.2).le z.2.property.2)
  have bounded(z:ℝ×Ratio):u z≤ -Real.log W.left:=neg_le_neg (Real.log_le_log W.positive z.2.property.1)
  have small:Tendsto (fun z:ℝ×Ratio=>u z/LogV z.1) sweep (𝓝 0):=by
    apply squeeze_zero' ?_ ?_ (large.const_div_atTop (-Real.log W.left))
    · filter_upwards [large.eventually_gt_atTop 0] with z hz
      exact div_nonneg (nonneg z) hz.le
    · filter_upwards [large.eventually_gt_atTop 0] with z hz
      exact div_le_div_of_nonneg_right (bounded z) hz.le
  have one:Tendsto (fun z:ℝ×Ratio=>1+u z/LogV z.1) sweep (𝓝 1):=by
    simpa only [add_zero] using (tendsto_const_nhds (x:=(1:ℝ))).add small
  apply one.congr'
  filter_upwards [large.eventually_gt_atTop 0,live] with z hz hr
  have log:LogV (z.2.val*z.1)=LogV z.1+u z:=by
    rw [LogV,LogV,Real.log_inv,Real.log_inv,Real.log_mul (positive z.2).ne' hr.ne'];unfold u;ring
  change 1+u z/LogV z.1=LogV (z.2.val*z.1)/LogV z.1
  rw [log];field_simp [hz.ne']

variable {G:Gauge}{g:ℝ→ℝ}(hG:G.Simple)(paid:Coupling G g)
include hG paid in
theorem signed:Tendsto (fun z:ℝ×Ratio=>g (z.2.val*z.1)/g z.1) sweep (𝓝 1):=by
  have b:0<G.slopeConstant⁻¹:=inv_pos.mpr (Gauge.slopeConstant_pos hG)
  have f:Tendsto (fun z:ℝ×Ratio=>z.1) sweep trail:=tendsto_fst
  have near:=paid.running.comp f
  have far:=paid.running.comp bothHomes
  have squared:Tendsto (fun z:ℝ×Ratio=>(g (z.2.val*z.1)/g z.1)^2) sweep (𝓝 1):=by
    have rate:=(far.div near b.ne').div geometry (by norm_num : (1:ℝ)≠0)
    rw [div_self b.ne',div_one] at rate
    apply rate.congr'
    filter_upwards [(PhysMS.to_log_zoom.comp f).eventually_gt_atTop 0,
      (PhysMS.to_log_zoom.comp bothHomes).eventually_gt_atTop 0,f.eventually paid.positive] with z hr ht hp
    change (LogV (z.2.val*z.1)*g (z.2.val*z.1)^2)/(LogV z.1*g z.1^2)/(LogV (z.2.val*z.1)/LogV z.1)=_
    change 0<LogV z.1 at hr
    change 0<LogV (z.2.val*z.1) at ht
    field_simp [hr.ne',ht.ne',hp.ne']
  have root:=Real.continuous_sqrt.continuousAt.tendsto.comp squared
  rw [Real.sqrt_one] at root
  apply root.congr'
  filter_upwards [f.eventually paid.positive,bothHomes.eventually paid.positive] with z a b
  exact Real.sqrt_sq (div_nonneg b.le a.le)

include hG paid in
theorem first:(fun z:ℝ×Ratio=>g (z.2.val*z.1)-g z.1)=o[sweep](fun z:ℝ×Ratio=>g z.1):=by
  apply isLittleO_iff.mpr;intro ε he
  have f:Tendsto (fun z:ℝ×Ratio=>z.1) sweep trail:=tendsto_fst
  filter_upwards [Metric.tendsto_nhds.mp (signed hG paid) ε he,f.eventually paid.positive] with z fee hp
  have b:|g (z.2.val*z.1)/g z.1-1|≤ε:=by simpa only [Real.dist_eq] using fee.le
  calc
    _=|(g (z.2.val*z.1)/g z.1-1)*g z.1|:=by rw [sub_mul,div_mul_cancel₀ _ hp.ne',one_mul,Real.norm_eq_abs]
    _=|g (z.2.val*z.1)/g z.1-1| * ‖g z.1‖:=by rw [abs_mul,Real.norm_eq_abs]
    _≤_:=mul_le_mul_of_nonneg_right b (norm_nonneg _)

end YM.Integration.WilsonPositionScaleLawKineticRatio
