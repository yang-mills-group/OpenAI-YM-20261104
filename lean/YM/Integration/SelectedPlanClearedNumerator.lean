import YM.Integration.SelectedPlanCenteredCoefficients
import YM.Integration.PositiveNormalizedRayJets
import YM.Integration.ActualAnalyticPlanVacuum
import YM.Integration.ActualRunPathNeighborhood

/-! Clear the singular kinetic factor in the original selected model action.
Every Plan coefficient, the complete same layer list and the original path/loop
remain in one explicit joint analytic numerator. The positive-side WholeAction
extension determines its exact degree-(2+k) jet, without being assumed analytic.
This is coefficient identification, not a coefficient-size estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedPlanClearedNumerator

open Function Filter Lattice Wilson RG Precision Exterior Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology ContDiff Classical BigOperators

variable {G : Gauge}

private theorem main_grade {n : Side} {c : Clip} {W : PathData G}
    {a A L : ℝ} (hW : W.Bounds c a A L) :
    GradeAt 2 (fun x : fieldDir G n 1 => mainTerm c W (represent x)) := by
  change GradeAt 2 (Extra.Iteration.Calibration.main W c)
  refine ⟨Extra.Iteration.Calibration.main_jet hW, ?_⟩
  intro i hi
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · ext v
    simpa only [iteratedFDeriv_zero_apply, _root_.zero_apply] using
      (Bulk.main_origin (m := n) c W hW)
  · ext v
    simp only [iteratedFDeriv_one_apply, Bulk.main_first c W hW,
      _root_.zero_apply]

variable (T : Run G) {N period order : ℕ}
    (P : Plan T.family N period order) (m : ℕ)

private theorem path_bounds (hm : m ≤ N) :
    (T.family.path.rep N period m).path.Bounds
      (T.family.path.levels.params m).clip (T.family.path.levels.params m).width
      (T.family.path.levels.params m).paths (T.family.path.levels.clock.loopCap m) := by
  have h : T.family.path.Conv N period m := T.makes.wilson.represents N period m hm
  rw [← h.clip]
  exact h.good.paths

/-- The full original action multiplied by the square of its coupling. -/
def numerator (z : ℝ × fieldDir G (T.family.side m period) 1) : ℂ :=
  ((mainTerm (T.family.path.levels.params m).clip
      (T.family.path.rep N period m).path (represent z.2) +
    ActualAnalyticPlanVacuum.vacuum T P m z.1 (represent z.2) +
    z.1 ^ 2 * Precision.loop (T.family.path.rep N period m).path
      (represent z.2) : ℝ) : ℂ)

variable {point : BudgetPoint} {rankCap : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers (P.layers m) point order rankCap width budget)

include H in
theorem numerator_grade (hm : m ≤ N) (hw : 0 < width) :
    GradeAt 2 (numerator T P m) := by
  have hm0 := (main_grade (path_bounds (period := period) T m hm)).coarse
    (g := fun z : ℝ × fieldDir G (T.family.side m period) 1 => z.2)
    contDiffAt_snd rfl
  have hv := (ActualAnalyticPlanVacuum.vacuum_grade T P m H hm hw).lower
    (show 2 ≤ 4 from by decide)
  have hg := GradeAt.shifts
    (fun z : ℝ × fieldDir G (T.family.side m period) 1 => z.1)
    contDiffAt_fst rfl 2
  have hl := GradeAt.unchecked
    ((Bulk.loop_smooth (T.family.path.levels.params m).clip
      (T.family.path.rep N period m).path (path_bounds (period := period) T m hm)).comp
      (0 : ℝ × fieldDir G (T.family.side m period) 1) contDiffAt_snd)
  have h := GradeAt.linear_contact Complex.ofRealCLM ((hm0.add hv).add (hg.scale hl))
  convert h using 1
  funext z
  rfl

include H in
private theorem divide {g : ℝ} (hg : 0 < g)
    (hb : 0 < (g ^ 2)⁻¹ + P.poly m g)
    (B : fieldDir G (T.family.side m period) 1)
    (hB : flags (T.family.path.levels.budget m).threshold (represent B) = ∅) :
    (g ^ 2)⁻¹ • numerator T P m (g, B) =
      (modelAction P m g (represent B) : ℂ) := by
  have ha := ActualAnalyticPlanVacuum.model_action T P m H hg hb (represent B) hB
  have hcancel : (g ^ 2)⁻¹ * g ^ 2 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 2 hg.ne')
  have he : (g ^ 2)⁻¹ *
      (mainTerm (T.family.path.levels.params m).clip
          (T.family.path.rep N period m).path (represent B) +
        ActualAnalyticPlanVacuum.vacuum T P m g (represent B) +
        g ^ 2 * Precision.loop (T.family.path.rep N period m).path (represent B)) =
      modelAction P m g (represent B) := by
    rw [mul_add, ← mul_assoc, hcancel, one_mul]
    exact ha
  simpa only [numerator, Complex.real_smul, ← Complex.ofReal_mul] using
    congrArg Complex.ofReal he

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} {A : NumericSchedule T.family J}
    {datum : LocalFormal.Datum T.family R}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain T.family.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum}

private theorem extension_value (M : AnalyticOutput caps Y K F)
    (B : fieldDir G (T.family.side datum.level datum.period) 1) :
    ∀ᶠ g : ℝ in 𝓝[>] 0, M.whole_action.extension g B =
      (g ^ 2)⁻¹ • numerator T M.plan datum.level (g, g • B) := by
  have hpoly : ContDiff ℝ ω (M.plan.poly datum.level) := by
    unfold Plan.poly
    exact ContDiff.sum fun e _ => contDiff_const.mul (contDiff_id.pow e)
  have hrad : ∀ᶠ g : ℝ in 𝓝 0, 0 < 1 + g ^ 2 * M.plan.poly datum.level g :=
    (continuous_const.add ((continuous_id.pow 2).mul hpoly.continuous)).continuousAt.eventually
      (lt_mem_nhds (by simp))
  have hscale : Tendsto (fun g : ℝ => g • B) (𝓝 0) (𝓝 0) := by
    simpa only [zero_smul] using
      (show Continuous (fun g : ℝ => g • B) from
        continuous_id.smul continuous_const).tendsto (0 : ℝ)
  have hchart : Tendsto (fun g : ℝ => represent (g • B)) (𝓝 0) (𝓝 1) := by
    have h := (RG02.Fk.represent_cont
      (G := G) (n := T.family.side datum.level datum.period)).tendsto 0
    rw [Precision.link_one] at h
    exact h.comp hscale
  have hflags := hchart.eventually (ProjectorNext.Equivariance.offFlags
    (G := G) (n := T.family.side datum.level datum.period)
    (T.family.path.levels.budget datum.level).threshold
    (T.family.path.levels.budget datum.level).threshold_pos)
  filter_upwards [M.whole_action.extension_value B,
    hrad.filter_mono nhdsWithin_le_nhds,
    hflags.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with g he hr hf hg
  have hg0 : 0 < g := hg
  have hfactor : 1 + g ^ 2 * M.plan.poly datum.level g =
      g ^ 2 * ((g ^ 2)⁻¹ + M.plan.poly datum.level g) := by
    rw [mul_add, mul_inv_cancel₀ (pow_ne_zero 2 hg0.ne')]
  have hb : 0 < (g ^ 2)⁻¹ + M.plan.poly datum.level g :=
    (mul_pos_iff_of_pos_left (pow_pos hg0 2)).mp (hfactor ▸ hr)
  exact he.trans (divide T M.plan datum.level M.vacuum hg0 hb (g • B) hf).symm

/-- Exact extraction from the positive-side extension of the same selected model. -/
theorem coefficient (M : AnalyticOutput caps Y K F)
    (B : fieldDir G (T.family.side datum.level datum.period) 1)
    (k : ℕ) (hk : k ≤ J.order) :
    jet (fun g : ℝ => M.whole_action.extension g B) k 1 =
      jet (numerator T M.plan datum.level) (2 + k) (1, B) := by
  exact PositiveNormalizedRayJets.joint_coefficient
    (numerator_grade T M.plan datum.level M.vacuum datum.below.le
      (A.output_width_pos datum.level)) B
    ((M.whole_action.extension_smooth B).of_le (by exact_mod_cast hk))
    (extension_value T M B)

/-- Every centered ground coefficient retains the complete explicit Plan numerator. -/
theorem centered_ground (M : AnalyticOutput caps Y K F)
    (x : TestSpace J.tests)
    (B : fieldDir G (T.family.side datum.level datum.period) 1)
    (k : ℕ) (hk : k ≤ J.order) :
    jet (numerator T M.plan datum.level) (2 + k) (1, B) -
        jet (numerator T M.plan datum.level) (2 + k) (1, 0) =
      Symmetry.Orbit.ground (datum.kernel Y) datum.forest datum.tag
        (F.colors x) J.order k B -
      Symmetry.Orbit.ground (datum.kernel Y) datum.forest datum.tag
        (F.colors x) J.order k 0 := by
  rw [← coefficient T M B k hk, ← coefficient T M 0 k hk]
  exact SelectedPlan.centered_eq_ground M x B k hk

end YM.Integration.SelectedPlanClearedNumerator
end
