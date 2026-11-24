import YM.Integration.PhysicalWilsonActionConvention
import YM.Integration.SelectedPlanTriangular

/-! Signed analytic output and the positive-side polar projection of its genuine selected plan. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalWilsonActionConvention
open Function Filter Lattice Wilson RG Precision Exterior Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology ContDiff Classical BigOperators

section Output
variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V]
    {R : Census V} {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C R}

structure SignedAnalyticOutput (caps : Handoff.OutputCapacities) (Y : Bulk.Chain C.path) (K : NumericPrices A)
    (F : AnalyticInput J A datum) where
  model : MarkedPackets J.tests G (C.side datum.level datum.period) R
  prescribed : PrescribedPackets Y datum F.colors model J.order
  rank_bounded : model.rankCap ≤ caps.packetRank
  power_bounded : model.powerCap ≤ caps.packetPower
  plan : Plan C datum.cutoff datum.period J.order
  fine_layers : plan.layers (datum.level + 1) = F.layers
  whole_action : SignedOutput Y J datum F.colors plan
  output_layers_paid : Render.permits (plan.layers datum.level) (A.outputNorm datum.level)
  vacuum : GradedVacuumLayers (plan.layers datum.level) (A.outputNorm datum.level)
    J.order caps.vacuumRank (A.outputWidth datum.level) (K.geometry datum.level)
  region : Comparison.Density.Testing.Region
    (fun v => (J.tests v).Mood) (C.side datum.level datum.period)
  coverOffset : ℕ
  coverSlope : ℕ
  cover_cost : Real.exp ((A.outputNorm datum.level).supportExponent * coverOffset) ≤
    K.geometry datum.level
  paid : model.Paid (A.outputNorm datum.level) F.outputAddresses region
    (fun v => F.outputRadii v / F.kernelCosts v)
    (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1))
    (A.outputWidth datum.level) (K.geometry datum.level) coverOffset coverSlope

def SignedAnalyticOutput.fine {caps : Handoff.OutputCapacities} {Y : Bulk.Chain C.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} (M : SignedAnalyticOutput caps Y K F) :
    FineWholeAction J datum F.colors (M.plan.layers (datum.level+1)) :=
  M.fine_layers.symm ▸ F.whole_input

end Output

variable {G : Gauge} (T : Run G)
open SelectedPlanClearedNumerator
section Plan
variable {N period order : ℕ} (P : Plan T.family N period order) (m : ℕ)
    {point : BudgetPoint} {rankCap : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers (P.layers m) point order rankCap width budget)

include H in
theorem divided {g : ℝ} (hg : 0 < g)
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

end Plan

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} {A : NumericSchedule T.family J}
    {datum : LocalFormal.Datum T.family R}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain T.family.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum}

private theorem extension_value (M : SignedAnalyticOutput caps Y K F)
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
  filter_upwards [M.whole_action.value B,
    hrad.filter_mono nhdsWithin_le_nhds,
    hflags.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with g he hr hf hg
  have hg0 : 0 < g := hg
  have hfactor : 1 + g ^ 2 * M.plan.poly datum.level g =
      g ^ 2 * ((g ^ 2)⁻¹ + M.plan.poly datum.level g) := by
    rw [mul_add, mul_inv_cancel₀ (pow_ne_zero 2 hg0.ne')]
  have hb : 0 < (g ^ 2)⁻¹ + M.plan.poly datum.level g :=
    (mul_pos_iff_of_pos_left (pow_pos hg0 2)).mp (hfactor ▸ hr)
  exact he.trans (divided T M.plan datum.level M.vacuum hg0 hb (g • B) hf).symm

/-- Exact extraction from the positive-side extension of the same selected model. -/
theorem coefficient (M : SignedAnalyticOutput caps Y K F)
    (B : fieldDir G (T.family.side datum.level datum.period) 1)
    (k : ℕ) (hk : k ≤ J.order) :
    jet (fun g : ℝ => M.whole_action.extension g B) k 1 =
      jet (numerator T M.plan datum.level) (2 + k) (1, B) := by
  exact PositiveNormalizedRayJets.joint_coefficient
    (numerator_grade T M.plan datum.level M.vacuum datum.below.le
      (A.output_width_pos datum.level)) B
    ((M.whole_action.smooth B).of_le (by exact_mod_cast hk))
    (extension_value T M B)


theorem centered_ground (M : SignedAnalyticOutput caps Y K F) (x : TestSpace J.tests)
    (B : fieldDir G (T.family.side datum.level datum.period) 1) (k : ℕ) (hk : k ≤ J.order) :
    jet (numerator T M.plan datum.level) (2+k) (1,B) -
      jet (numerator T M.plan datum.level) (2+k) (1,0) =
      Symmetry.Orbit.ground (datum.kernel Y) datum.forest datum.tag (F.colors x) J.order k 0 -
        Symmetry.Orbit.ground (datum.kernel Y) datum.forest datum.tag (F.colors x) J.order k B := by
  rw [← coefficient T M B k hk, ← coefficient T M 0 k hk]
  exact M.whole_action.centered x B k hk

end YM.Integration.PhysicalWilsonActionConvention
end
