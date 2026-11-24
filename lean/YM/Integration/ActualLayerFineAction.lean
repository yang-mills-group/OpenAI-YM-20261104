import YM.Integration.ActualGradedVacuum
import YM.Integration.ActualRunPathNeighborhood
import YM.Integration.FullQLocalRenderedStepData
import Mathlib.Analysis.Analytic.Order

/-!
A genuine graded layer list supplies the complete fine action on the
original Run path. The same analytic extension is used before every
independent test tuple. Every original packet action and root is retained.

This theorem accepts the actual layer list and its common-vacuum colors.
It does not identify a retuned list with an earlier Plan chart, absorb a
kinetic correction, or discard the physical quiet or marked residual.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace YM.Integration.ActualLayerFineAction

open Function Filter Finset Lattice Wilson RG Marker Exterior
open PhysicalNext.Repeat.Legato
open Comparison.RG02 Comparison.RG02.Assembly
open IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal
open scoped Classical Topology BigOperators ContDiff

variable {G : Gauge}

/-- The original unmasked action is summable, using the actual per-root
atom budgets of this same layer list. -/
theorem action_summable {n : Side} {layers : List (Piece G n)}
    {p : BudgetPoint} {order rankCap : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers layers p order rankCap width budget)
    (hwidth : 0 < width) (a : Piece G n) (ha : a ∈ layers)
    (U : Config G n) :
    Summable (fun i : ℕ => a.packet.action i U) := by
  let f (o : Site n) (i : ℕ) : ℝ :=
    if (a.packet.labels i).site = o then (H.packets.atom a i).budget width else 0
  have hs (o : Site n) : Summable (f o) := by
    simpa only [f, Atom.budget] using (H.packets.exponential a ha o).2.1
  have ht := summable_sum (s := Finset.univ) (fun o _ => hs o)
  have hb : Summable (fun i : ℕ => (H.packets.atom a i).budget width) := by
    convert ht using 1
    funext i
    simp [f]
  have hu := NativeBoundedAtomSeries.value_summable
    (H.packets.atom a) (fun i => (a.packet.labels i).site) hwidth
    (cap := a.rank) (fun _ => le_rfl) hb U
  exact hu.congr (fun i => (H.packets.original_action a ha i U).symm)

private theorem path_bounds (R : Run G) (N period level : ℕ) (hlevel : level < N) :
    (R.family.path.rep N period (level + 1)).path.Bounds
      (R.family.path.levels.params (level + 1)).clip
      (R.family.path.levels.params (level + 1)).width
      (R.family.path.levels.params (level + 1)).paths
      (R.family.path.levels.clock.loopCap (level + 1)) := by
  have h : R.family.path.Conv N period (level + 1) :=
    R.makes.wilson.represents N period (level + 1) hlevel
  rw [← h.clip]
  exact h.good.paths

private theorem main_grade {n : Side} (P : PathData G) (c : Clip)
    {σ C Λ : ℝ} (hP : P.Bounds c σ C Λ) :
    GradeAt 2 (Extra.Iteration.Calibration.main (n := n) P c) := by
  refine ⟨Extra.Iteration.Calibration.main_jet hP, ?_⟩
  intro i hi
  interval_cases i
  · ext x
    simpa only [iteratedFDeriv_zero_apply, zero_apply]
      using Bulk.main_origin (m := n) c P hP
  · ext x
    rw [iteratedFDeriv_one_apply, Bulk.main_first c P hP]
    rfl

private def curve (R : Run G) (N period level : ℕ)
    (layers : List (Piece G (R.family.side (level + 1) period)))
    (B : fieldDir G (R.family.side (level + 1) period) 1)
    (g : ℝ) : ℝ :=
  Precision.mainTerm (R.family.path.levels.params (level + 1)).clip
      (R.family.path.rep N period (level + 1)).path
      (Precision.represent (g • B)) +
    ActualGradedVacuum.restored layers g (Precision.represent (g • B))

private theorem curve_grade (R : Run G) (N period level : ℕ)
    (hlevel : level < N)
    {layers : List (Piece G (R.family.side (level + 1) period))}
    {p : BudgetPoint} {order rankCap : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers layers p order rankCap width budget)
    (hwidth : 0 < width)
    (B : fieldDir G (R.family.side (level + 1) period) 1) :
    GradeAt 2 (curve R N period level layers B) := by
  have hline : ContDiff ℝ ω (fun g : ℝ => g • B) :=
    contDiff_id.smul contDiff_const
  have hmain := (main_grade
    (R.family.path.rep N period (level + 1)).path
    (R.family.path.levels.params (level + 1)).clip
    (path_bounds R N period level hlevel)).coarse hline.contDiffAt (by simp)
  have hjoint : ContDiff ℝ ω (fun g : ℝ => (g, g • B)) :=
    contDiff_id.prodMk hline
  have hv := ((ActualGradedVacuum.restored_grade H hwidth).lower
    (by decide : 2 ≤ 5)).coarse hjoint.contDiffAt (by simp)
  exact hmain.add hv

private theorem divide_two {f : ℝ → ℝ} (hf : GradeAt 2 f) :
    ∃ Q : ℝ → ℝ, ContDiffAt ℝ ω Q 0 ∧
      ∀ᶠ g : ℝ in 𝓝 0, f g = g ^ 2 * Q g := by
  obtain ⟨Q, hQ, he⟩ :=
    hf.smooth.analyticAt.exists_eventuallyEq_sum_add_pow_mul 2
  refine ⟨Q, hQ.contDiffAt, he.mono fun g hg => ?_⟩
  have hz : (∑ i ∈ Finset.range 2,
      (g ^ i / (i.factorial : ℝ)) • iteratedDeriv i f 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [iteratedDeriv_eq_iteratedFDeriv, hf.vanish i (Finset.mem_range.mp hi)]
    simp
  rw [hz, zero_add] at hg
  simpa only [smul_eq_mul] using hg

/-- Complete fine-action authentication for the supplied graded list and
its literal common vacuum. Both extensions are the same function, before
all test tuples. The original native path and every layer are retained. -/
theorem whole_action (R : Run G)
    {V : Type} [DecidableEq V] [Fintype V]
    (marks : Census V) (J : FullQLocal.RenderedStep.Request V)
    (datum : LocalFormal.Datum R.family marks)
    {layers : List (Piece G (R.family.side (datum.level + 1) datum.period))}
    {p : BudgetPoint} {order rankCap : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers layers p order rankCap width budget)
    (hwidth : 0 < width)
    (colors : TestSpace J.tests →
      Bulk.Colors marks G (R.family.side (datum.level + 1) datum.period))
    (packets : MarkedPackets J.tests G
      (R.family.side (datum.level + 1) datum.period) marks)
    (hColors : InputColors colors packets)
    (hVac : ∀ x, (colors x).vac = ActualGradedVacuum.restored layers) :
    Nonempty (FullQLocal.RenderedStep.FineWholeAction J datum colors layers) := by
  have hex (B : fieldDir G (R.family.side (datum.level + 1) datum.period) 1) :
      ∃ Q : ℝ → ℝ, ContDiffAt ℝ ω Q 0 ∧
        ∀ᶠ g : ℝ in 𝓝 0,
          curve R datum.cutoff datum.period datum.level layers B g = g ^ 2 * Q g :=
    divide_two (curve_grade R datum.cutoff datum.period datum.level datum.below H hwidth B)
  choose Q hQ hQeq using hex
  let E : ℝ →
      fieldDir G (R.family.side (datum.level + 1) datum.period) 1 → ℂ :=
    fun g B => ((Q B g +
      Precision.loop
        (R.family.path.rep datum.cutoff datum.period (datum.level + 1)).path
        (Precision.represent (g • B)) : ℝ) : ℂ)
  have hE (B : fieldDir G (R.family.side (datum.level + 1) datum.period) 1) :
      ContDiffAt ℝ J.order (fun g : ℝ => E g B) 0 := by
    have hline : ContDiff ℝ ω (fun g : ℝ => g • B) :=
      contDiff_id.smul contDiff_const
    have hloop0 := Bulk.loop_smooth
      (m := R.family.side (datum.level + 1) datum.period)
      (R.family.path.levels.params (datum.level + 1)).clip
      (R.family.path.rep datum.cutoff datum.period (datum.level + 1)).path
      (path_bounds R datum.cutoff datum.period datum.level datum.below)
    have hloopAt : ContDiffAt ℝ ω
        (Precision.loop
          (R.family.path.rep datum.cutoff datum.period (datum.level + 1)).path ∘
            Precision.represent) ((fun g : ℝ => g • B) 0) := by
      simpa only [zero_smul] using hloop0
    have hloop := hloopAt.comp 0 hline.contDiffAt
    exact (((hQ B).add hloop).continuousLinearMap_comp
      Complex.ofRealCLM).of_le le_top
  refine ⟨{
    standard := fun x => ⟨hColors.well x, by
      rw [hVac x]
      exact ActualGradedVacuum.restored_grade H hwidth⟩
    input_summable := action_summable H hwidth
    inputExtension := E
    formalInputExtension := fun _ => E
    input_extension_value := ?_
    formal_input_extension_value := ?_
    input_extension_smooth := hE
    formal_input_extension_smooth := fun _ => hE
    input_whole := by intros; rfl
  }⟩
  · intro B
    have hline : Tendsto (fun g : ℝ => g • B) (𝓝 0) (𝓝 0) := by
      simpa only [zero_smul] using
        (show Continuous (fun g : ℝ => g • B) from
          continuous_id.smul continuous_const).tendsto (0 : ℝ)
    have hp := hline.eventually
      (ActualRunPathNeighborhood.represented R datum.cutoff datum.period datum.level)
    filter_upwards [(hQeq B).filter_mono nhdsWithin_le_nhds,
      hp.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with g hg hpath hpos
    have hgn : g ≠ 0 := (show 0 < g from hpos).ne'
    have hquot : Q B g =
        (g ^ 2)⁻¹ * curve R datum.cutoff datum.period datum.level layers B g := by
      rw [hg, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hgn), one_mul]
    change ((Q B g + _ : ℝ) : ℂ) = _
    apply congrArg Complex.ofReal
    rw [hquot, hpath.2 ((g ^ 2)⁻¹)]
    unfold curve
    rw [ActualGradedVacuum.restored_eq H hgn, mul_add, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero 2 hgn), one_mul]
    ring
  · intro x B
    filter_upwards [(hQeq B).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with g hg hpos
    have hgn : g ≠ 0 := (show 0 < g from hpos).ne'
    have hquot : Q B g =
        (g ^ 2)⁻¹ * curve R datum.cutoff datum.period datum.level layers B g := by
      rw [hg, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hgn), one_mul]
    change ((Q B g + _ : ℝ) : ℂ) =
      (((g ^ 2)⁻¹ *
        (Precision.mainTerm (R.family.path.levels.params (datum.level + 1)).clip
          (R.family.path.rep datum.cutoff datum.period (datum.level + 1)).path
          (Precision.represent (g • B)) +
          (colors x).vac g (Precision.represent (g • B))) + _ : ℝ) : ℂ)
    rw [hVac x]
    change ((Q B g + _ : ℝ) : ℂ) =
      (((g ^ 2)⁻¹ * curve R datum.cutoff datum.period datum.level layers B g + _ : ℝ) : ℂ)
    rw [hquot]

end YM.Integration.ActualLayerFineAction
end
