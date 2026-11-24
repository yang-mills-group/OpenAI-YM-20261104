import YM.Integration.WilsonFundedMeasuredWindow
import YM.Integration.WilsonPhysicalWindowPosteriorPrice

/-! Both sides of the cutoff/continuum coupling comparison at every physical
reporting radius, uniformly in all the regulators over that report. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalCutoffCurrency

open Filter Function Real Lattice Wilson RG RG16 RG16.Literal RG16.Guarding Pert.Asymptotics
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE Trace.Pilot
open scoped Topology

variable {G : Gauge} (R : Run G) (hG : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (hB : 0 < B)

include slow hB in
theorem temperature (g : ℝ → ℝ) (H : Coupling G g) :
    let m := WilsonMeasuredWindow.stop R.family.path.levels hG B
    Tendsto (fun r => R.family.path.levels.clock.hatBeta (m r)*(g r)^2)
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
  let m := WilsonMeasuredWindow.stop R.family.path.levels hG B
  let β := R.family.path.levels.clock.hatBeta
  let b := R.family.path.levels.clock.bar
  let s := R.family.S.scale
  let c := G.slopeConstant
  have date : Height R.family.S trail LogV m 1 :=
    WilsonMeasuredWindow.measured_stop_height R.family.path.levels hG B
      (WilsonFundedMeasuredWindow.paced R slow) hB PhysMS.to_log_zoom PhysMS.length_rate
  have damp : Tendsto (fun r => b/LogV r) trail (𝓝 0) :=
    (tendsto_const_nhds (x:=b)).div_atTop PhysMS.to_log_zoom
  have temp : Tendsto (fun r => β (m r)/LogV r) trail (𝓝 c) := by
    have v := damp.add ((tendsto_const_nhds (x:=c)).mul date.pace)
    rw [mul_one,zero_add] at v
    exact v.congr fun r=>by change b/LogV r+c*(s (m r)/LogV r)=(b+c*s (m r))/LogV r; ring
  have positive : 0 < c := Gauge.slopeConstant_pos hG
  have both := temp.mul H.running
  change Tendsto _ trail (𝓝 (c*c⁻¹)) at both
  rw [mul_inv_cancel₀ positive.ne'] at both
  apply both.congr'
  filter_upwards [PhysMS.to_log_zoom.eventually_gt_atTop 0] with r hr
  change (β (m r)/LogV r)*(LogV r*(g r)^2)=β (m r)*(g r)^2
  field_simp [hr.ne']

private theorem root_le {x y : ℝ} (hy : 0 ≤ y) (square : x^2 ≤ y^2) : x ≤ y := by
  by_contra! bad
  have strict := mul_pos (sub_pos.mpr bad) (by linarith only [hy,bad] : 0<x+y)
  nlinarith only [strict,square]

include slow hB in
theorem band (g : ℝ → ℝ) (H : Coupling G g) :
    let m := WilsonMeasuredWindow.stop R.family.path.levels hG B
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ N n, m r ≤ N →
      g r / 2 ≤ regulatorRun R.family N n (m r) ∧ regulatorRun R.family N n (m r) ≤ 2*g r := by
  let m := WilsonMeasuredWindow.stop R.family.path.levels hG B
  let β := R.family.path.levels.clock.hatBeta
  have limit := temperature R hG slow hB g H
  filter_upwards [H.positive,(tendsto_order.mp limit).1 _ (by norm_num : (1/2:ℝ)<1),
    (tendsto_order.mp limit).2 _ (by norm_num : (1:ℝ)<2)] with r hr low high
  intro N n live
  let v := regulatorRun R.family N n (m r)
  let b := R.family.path.β N n (m r)
  have bpos : 0 < b := Overlay.beta_positive R.makes.wilson live
  have actual : β (m r)/2 ≤ b ∧ b ≤ 2*β (m r) := (R.makes.wilson.represents N n (m r) live).band
  have vpos : 0 < v := g_pos R.makes live
  have account : v^2*b=1 := cashable R.family R.makes live
  change 1/2 < β (m r)*(g r)^2 at low
  change β (m r)*(g r)^2 < 2 at high
  constructor
  · apply root_le vpos.le
    apply (mul_le_mul_iff_of_pos_right bpos).mp
    rw [account]
    nlinarith only [mul_le_mul_of_nonneg_right actual.2 (sq_nonneg (g r)),high]
  · apply root_le (by positivity)
    apply (mul_le_mul_iff_of_pos_right bpos).mp
    rw [account]
    nlinarith only [mul_le_mul_of_nonneg_right actual.1 (sq_nonneg (g r)),low]

end YM.Integration.WilsonPhysicalCutoffCurrency

