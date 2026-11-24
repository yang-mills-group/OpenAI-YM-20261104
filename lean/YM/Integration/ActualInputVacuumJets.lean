import YM.Integration.FullQLocalNumericStepData
import YM.Integration.ActualGradedVacuum
import YM.Integration.ActualRunPathNeighborhood
import YM.Integration.PositiveNormalizedRayJets
import YM.Integration.ActualJointJetContact

/-! The full fine action identifies precisely the finite vacuum jets needed by
Fk. This does not replace an arbitrary input vacuum by the layer sum as a full
function. The original Run, finite layer list and every independent test remain
fixed, and the singular factor contributes the explicit degree shift by two. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualInputVacuumJets

open Function Filter Lattice Wilson RG Precision Exterior Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology ContDiff Classical BigOperators

variable {G : Gauge} (T : Run G)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} {A : NumericSchedule T.family J}
    {datum : LocalFormal.Datum T.family R}
    (F : AnalyticInput J A datum)

private def error (x : TestSpace J.tests)
    (B : fieldDir G (T.family.side (datum.level + 1) datum.period) 1)
    (g : ℝ) : ℝ :=
  (F.whole_input.formalInputExtension x g B -
    F.whole_input.inputExtension g B).re

private theorem error_value (x : TestSpace J.tests)
    (B : fieldDir G (T.family.side (datum.level + 1) datum.period) 1) :
    ∀ᶠ g : ℝ in 𝓝[>] 0, error T F x B g =
      (g ^ 2)⁻¹ •
        ((Bulk.projected (F.colors x).vac -
          Bulk.projected (ActualGradedVacuum.restored F.layers)) (g, g • B)) := by
  have hscale : Tendsto (fun g : ℝ => g • B) (𝓝 0) (𝓝 0) := by
    simpa only [zero_smul] using
      (show Continuous (fun g : ℝ => g • B) from
        continuous_id.smul continuous_const).tendsto (0 : ℝ)
  have hpath := hscale.eventually (ActualRunPathNeighborhood.represented T
    datum.cutoff datum.period datum.level)
  filter_upwards [F.whole_input.formal_input_extension_value x B,
    F.whole_input.input_extension_value B,
    hpath.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with g hf hi hp hg
  have hg0 : 0 < g := hg
  have hcancel : (g ^ 2)⁻¹ * g ^ 2 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 2 hg0.ne')
  unfold error
  rw [hf, hi, ← Complex.ofReal_sub, Complex.ofReal_re,
    hp.2 ((g ^ 2)⁻¹)]
  simp only [Integral.localClassic, Integral.temperature, Pi.sub_apply,
    Bulk.projected, smul_eq_mul]
  rw [ActualGradedVacuum.restored_eq F.vacuum hg0.ne', mul_sub,
    ← mul_assoc, hcancel, one_mul]
  ring

private theorem error_smooth (x : TestSpace J.tests)
    (B : fieldDir G (T.family.side (datum.level + 1) datum.period) 1)
    (k : ℕ) (hk : k ≤ J.order) :
    ContDiffAt ℝ k (error T F x B) 0 := by
  have hf := (F.whole_input.formal_input_extension_smooth x B).of_le
    (show (k : WithTop ℕ∞) ≤ J.order by exact_mod_cast hk)
  have hi := (F.whole_input.input_extension_smooth B).of_le
    (show (k : WithTop ℕ∞) ≤ J.order by exact_mod_cast hk)
  exact Complex.reCLM.contDiff.contDiffAt.comp 0 (hf.sub hi)

private theorem error_jet (x : TestSpace J.tests)
    (B : fieldDir G (T.family.side (datum.level + 1) datum.period) 1)
    (k : ℕ) (hk : k ≤ J.order) : jet (error T F x B) k 1 = 0 := by
  have hf := (F.whole_input.formal_input_extension_smooth x B).of_le
    (show (k : WithTop ℕ∞) ≤ J.order by exact_mod_cast hk)
  have hi := (F.whole_input.input_extension_smooth B).of_le
    (show (k : WithTop ℕ∞) ≤ J.order by exact_mod_cast hk)
  have he : jet (fun g : ℝ => F.whole_input.formalInputExtension x g B -
      F.whole_input.inputExtension g B) k 1 = 0 := by
    change jet ((fun g : ℝ => F.whole_input.formalInputExtension x g B) -
      (fun g : ℝ => F.whole_input.inputExtension g B)) k 1 = 0
    simp only [jet, iteratedFDeriv_sub_apply hf hi, _root_.sub_apply, smul_sub]
    exact sub_eq_zero.mpr (F.whole_input.input_whole x B k hk).symm
  change jet (Complex.reCLM ∘ (fun g : ℝ =>
    F.whole_input.formalInputExtension x g B - F.whole_input.inputExtension g B)) k 1 = 0
  rw [← jet_apply_left Complex.reCLM _ k (hf.sub hi) 1, he, map_zero]

/-- Every required shifted unit-slice vacuum coefficient comes from the
complete original fine layer list. No global equality of vacua is used. -/
theorem unit_coefficient (x : TestSpace J.tests)
    (B : fieldDir G (T.family.side (datum.level + 1) datum.period) 1)
    (k : ℕ) (hk : k ≤ J.order) :
    jet (Bulk.projected (F.colors x).vac) (2 + k) (1, B) =
      jet (Bulk.projected (ActualGradedVacuum.restored F.layers)) (2 + k) (1, B) := by
  have hf := (F.whole_input.standard x).2
  have hi := ActualGradedVacuum.restored_grade F.vacuum
    (A.input_width_pos datum.level)
  have h := PositiveNormalizedRayJets.joint_coefficient
    ((hf.sub hi).lower (by omega : 2 ≤ 5)) B
    (error_smooth T F x B k hk) (error_value T F x B)
  rw [error_jet T F x B k hk] at h
  have hz := h.symm
  simp only [jet, iteratedFDeriv_sub_apply
    (hf.smooth.of_le le_top) (hi.smooth.of_le le_top),
    _root_.sub_apply, smul_sub] at hz
  exact sub_eq_zero.mp hz

/-- The finite action authentication determines full joint contact through
order J.order+2, including all fields and the actual coupling coordinate. -/
theorem joint_contact (x : TestSpace J.tests) :
    GradeAt (2 + J.order + 1)
      (Bulk.projected (F.colors x).vac -
        Bulk.projected (ActualGradedVacuum.restored F.layers)) := by
  apply ActualJointJetContact.grade_sub_of_shifted_slices _ _ 2 J.order
    ((F.whole_input.standard x).2.lower (by omega))
    ((ActualGradedVacuum.restored_grade F.vacuum
      (A.input_width_pos datum.level)).lower (by omega))
  intro k hk B
  exact unit_coefficient T F x B k hk

end YM.Integration.ActualInputVacuumJets
end
