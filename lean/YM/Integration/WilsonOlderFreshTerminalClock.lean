import YM.Integration.WilsonIndependentCapturedPages

/-! The elected independent stop pays the physical horizon-zero contraction
and fits the dated physical weak window at the same measured coupling. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOlderFreshTerminalClock
open Filter PhysicalNext PhysicalNext.Repeat Legato Pert.Asymptotics
open WilsonPositionProgramReporterBand WilsonIndependentCapturedPages
open scoped Classical Topology
variable {G : Gauge} (R : Run G) (D : XSpace.Run)

theorem original {stage u d : ℕ} {B : Band R D stage} (v : Stop R D B u d)
    (P loss : ℕ) (depth : 4*(P+loss) ≤ d) :
    ∀ᶠ t : ℕ in atTop, u ≤ v.date t ∧ ∀ N per : ℕ, B.reporter+t ≤ N →
      let b := B.reporter+t
      let g := regulatorRun R.family N per b
      let H := R.family.path.levels.clock.hatBeta b
      let span := R.family.S.scale b-R.family.S.scale (v.date t)
      0 < g ∧ g ≤ 1 ∧ 8*((P:ℝ)+loss)*Real.log g⁻¹ ≤ span ∧
        span ≤ (4*(2*(d:ℝ)+1))*Real.log (4*H)+(1+Real.log H) := by
  filter_upwards [v.heard] with t heard
  refine ⟨heard.1,?_⟩
  intro N per cut b g H span
  obtain ⟨gp,small,mesh,roof⟩ := heard.2 N per cut
  have cpos := R.family.S.a_pos b
  have vpos := R.family.S.a_pos (v.date t)
  have gross := Real.log_le_log (div_pos cpos vpos) mesh
  have distance : -span ≤ 2*(d:ℝ)*Real.log g := by
    change Real.log (R.family.S.a b/R.family.S.a (v.date t)) ≤ Real.log ((g^d)^2) at gross
    rw [WilsonIndependentCapturedDates.mesh R b (v.date t), Real.log_pow, Real.log_pow] at gross
    change -(R.family.S.scale b-R.family.S.scale (v.date t)) ≤ _
    push_cast at gross
    linarith only [gross]
  have lg : 0 ≤ -Real.log g := neg_nonneg.mpr (Real.log_nonpos gp.le small)
  have enough : 8*((P:ℝ)+loss) ≤ 2*(d:ℝ) := by exact_mod_cast (by omega : 8*(P+loss) ≤ 2*d)
  have hp : 1 ≤ H := (R.family.path.levels.fits.delayed b).le
  have beta := (R.makes.wilson.represents N per b cut).band.2
  change (R.family.path.rep N per b).beta ≤ 2*H at beta
  have rt : g⁻¹ ≤ 4*H := by
    change ((Real.sqrt (R.family.path.rep N per b).beta)⁻¹)⁻¹ ≤ _
    rw [inv_inv]
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith only [hp,beta,sq_nonneg (H-1)]
  refine ⟨gp,small,?_,?_⟩
  · rw [Real.log_inv]
    exact (mul_le_mul_of_nonneg_right enough lg).trans (by linarith only [distance])
  · have upper := Real.log_le_log (inv_pos.mpr gp) rt
    have pad : 0 ≤ 1+Real.log H := by linarith [Real.log_nonneg hp]
    refine (roof.trans (mul_le_mul_of_nonneg_left upper (by positivity))).trans ?_
    exact le_add_of_nonneg_right pad

end YM.Integration.WilsonOlderFreshTerminalClock
