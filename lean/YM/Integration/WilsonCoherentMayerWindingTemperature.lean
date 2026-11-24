import YM.Integration.WilsonMovingMentorBentTemperature
import YM.Integration.WilsonCoherentMayerWindingGrades

/-! A uniform evaluation radius at the actual inherited temperature. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerWindingTemperature
open Filter RG Push ConnectedActivityE6 PhysicalNext.Repeat.Legato
open scoped Topology

theorem purchased {G:Gauge} (R:Run G) (simple:G.Simple):
    ∀ᶠ m:ℕ in atTop, ∀ N per, m≤N →
      ‖(Coat.gStep (R.family.path.rep N per m).beta:ℂ)‖≤1/2:=by
  let A:=R.alloy.B.a
  have rise:Tendsto A.clock.hatBeta atTop atTop:=
    tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [rise.eventually_ge_atTop 8] with m early
  intro N per hm
  let β:=(R.family.path.rep N per m).beta
  have hb:4≤β:=by
    have h:A.clock.hatBeta m/2≤β:=(R.makes.wilson.represents N per m hm).band.1
    linarith
  have hs:(2:ℝ)≤Real.sqrt β:=(Real.le_sqrt (by norm_num) (by linarith)).2 (by norm_num;exact hb)
  rw [Complex.norm_real,Real.norm_eq_abs]
  change |(Real.sqrt β)⁻¹|≤1/2
  rw [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg β)),one_div]
  simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num) hs)

end YM.Integration.WilsonCoherentMayerWindingTemperature
