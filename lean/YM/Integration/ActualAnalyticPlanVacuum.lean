import YM.Integration.ActualGradedVacuum
import YM.Integration.ActualProducedVacuumRestoration
import YM.AllOrder.Laplace.Spin
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! A concrete analytic vacuum for the original Run's selected Plan.
The full kinetic correction is retained. The signed coupling chart agrees
with the original positive square-root coupling on the physical domain.
The resulting joint grade is four, not the stronger standard grade five.
No equality of the Plan's prediction and the actual beta is asserted. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualAnalyticPlanVacuum
open Function Filter Lattice Wilson RG Precision Exterior
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison.Global FullQLocal Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology BigOperators ContDiff Classical

variable {G : Gauge}

private theorem main_grade {n : Side} {c : Clip} {W : PathData G}
    {a A Λ : ℝ} (hW : W.Bounds c a A Λ) :
    GradeAt 2 (fun x : fieldDir G n 1 => mainTerm c W (represent x)) := by
  change GradeAt 2 (Extra.Iteration.Calibration.main W c)
  refine ⟨Extra.Iteration.Calibration.main_jet hW, ?_⟩
  intro i hi
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · ext v
    simpa only [iteratedFDeriv_zero_apply, zero_apply] using
      (Bulk.main_origin (m := n) c W hW)
  · ext v
    simp only [iteratedFDeriv_one_apply, Bulk.main_first c W hW,
      zero_apply]

variable (R : Run G) {N period order : ℕ}
    (P : Plan R.family N period order) (m : ℕ)

private theorem poly_analytic : ContDiff ℝ ω (P.poly m) := by
  unfold Plan.poly
  exact ContDiff.sum fun e _ => contDiff_const.mul (contDiff_id.pow e)

def radicand (g : ℝ) : ℝ := 1 + g ^ 2 * P.poly m g

def coupling (g : ℝ) : ℝ := g / Real.sqrt (radicand R P m g)

private theorem radicand_zero : radicand R P m 0 = 1 := by
  simp [radicand]

private theorem radicand_analytic : ContDiff ℝ ω (radicand R P m) :=
  contDiff_const.add ((contDiff_id.pow 2).mul (poly_analytic R P m))

theorem coupling_zero : coupling R P m 0 = 0 := by
  simp [coupling]

theorem coupling_analytic : ContDiffAt ℝ ω (coupling R P m) 0 := by
  unfold coupling
  exact contDiffAt_id.div
    ((radicand_analytic R P m).contDiffAt.sqrt
      (by rw [radicand_zero]; exact one_ne_zero))
    (by rw [radicand_zero, Real.sqrt_one]; exact one_ne_zero)

private theorem radicand_eq {g : ℝ} (hg : g ≠ 0) :
    radicand R P m g = g ^ 2 * ((g ^ 2)⁻¹ + P.poly m g) := by
  rw [radicand, mul_add, mul_inv_cancel₀ (pow_ne_zero 2 hg)]

/-- The signed analytic extension is exactly the original Plan coupling
at every positive physical input with positive predicted beta. -/
theorem coupling_eq_gain {g : ℝ} (hg : 0 < g)
    (hb : 0 < (g ^ 2)⁻¹ + P.poly m g) :
    coupling R P m g = Currency.gain ((g ^ 2)⁻¹ + P.poly m g) := by
  rw [coupling, radicand_eq R P m hg.ne',
    Real.sqrt_mul' (g ^ 2) hb.le, Real.sqrt_sq_eq_abs, abs_of_pos hg]
  unfold Currency.gain
  field_simp [hg.ne']

private theorem path_bounds (hm : m ≤ N) :
    (R.family.path.rep N period m).path.Bounds
      (R.family.path.levels.params m).clip (R.family.path.levels.params m).width
      (R.family.path.levels.params m).paths (R.family.path.levels.clock.loopCap m) := by
  have h : R.family.path.Conv N period m :=
    R.makes.wilson.represents N period m hm
  rw [← h.clip]
  exact h.good.paths

def kinetic (g : ℝ) (U : Config G (R.family.side m period)) : ℝ :=
  g ^ 2 * P.poly m g * mainTerm (R.family.path.levels.params m).clip
    (R.family.path.rep N period m).path U

/-- The complete beta correction has joint grade four. It is retained,
rather than silently removed to assert standard grade five. -/
theorem kinetic_grade (hm : m ≤ N) : GradeAt 4 (Bulk.projected (kinetic R P m)) := by
  change GradeAt 4 (fun y : ℝ × fieldDir G (R.family.side m period) 1 =>
    y.1 ^ 2 * P.poly m y.1 * mainTerm (R.family.path.levels.params m).clip
      (R.family.path.rep N period m).path (represent y.2))
  have hg := GradeAt.shifts
    (fun y : ℝ × fieldDir G (R.family.side m period) 1 => y.1)
    contDiffAt_fst rfl 2
  have hp := GradeAt.unchecked
    ((poly_analytic R P m).contDiffAt.comp
      (0 : ℝ × fieldDir G (R.family.side m period) 1) contDiffAt_fst)
  have hw := (main_grade (n := R.family.side m period)
    (path_bounds (period := period) R m hm)).coarse
    (g := fun y : ℝ × fieldDir G (R.family.side m period) 1 => y.2)
    contDiffAt_snd rfl
  simpa only [smul_eq_mul, Function.comp_def] using (hg.scale hp).scale hw

def vacuum (g : ℝ) (U : Config G (R.family.side m period)) : ℝ :=
  kinetic R P m g U + radicand R P m g *
    ActualGradedVacuum.restored (P.layers m) (coupling R P m g) U

variable {point : BudgetPoint} {rankCap : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers (P.layers m) point order rankCap width budget)

include H

theorem vacuum_grade (hm : m ≤ N) (hwidth : 0 < width) :
    GradeAt 4 (Bulk.projected (vacuum R P m)) := by
  let changeCoupling (y : ℝ × fieldDir G (R.family.side m period) 1) :=
    (coupling R P m y.1, y.2)
  have hs : ContDiffAt ℝ ω changeCoupling 0 :=
    ((coupling_analytic R P m).comp
      (0 : ℝ × fieldDir G (R.family.side m period) 1) contDiffAt_fst).prodMk
      contDiffAt_snd
  have hz : changeCoupling 0 = 0 := by simp [changeCoupling, coupling_zero]
  have hl := (ActualGradedVacuum.restored_grade H hwidth).coarse
    (g := changeCoupling) hs hz
  have hr := GradeAt.unchecked
    ((radicand_analytic R P m).contDiffAt.comp
      (0 : ℝ × fieldDir G (R.family.side m period) 1) contDiffAt_fst)
  have hb : GradeAt 5 (fun y : ℝ × fieldDir G (R.family.side m period) 1 =>
      radicand R P m y.1 *
        ActualGradedVacuum.restored (P.layers m) (coupling R P m y.1) (represent y.2)) := by
    simpa only [changeCoupling, Bulk.projected, Function.comp_def, smul_eq_mul] using
      hr.scale hl
  change GradeAt 4 (Bulk.projected (kinetic R P m) +
    fun y : ℝ × fieldDir G (R.family.side m period) 1 =>
      radicand R P m y.1 *
        ActualGradedVacuum.restored (P.layers m) (coupling R P m y.1) (represent y.2))
  exact (kinetic_grade R P m hm).add (hb.lower (by decide : 4 ≤ 5))

theorem vacuum_gauge (hm : m ≤ N) (g : ℝ) : GaugeInvariant (vacuum R P m g) := by
  intro t U
  unfold vacuum kinetic
  rw [Work.F05.mainTerm_gauge (path_bounds (period := period) R m hm),
    ActualGradedVacuum.restored_gauge H (coupling R P m g)]

theorem vacuum_envelope (hm : m ≤ N) (hwidth : 0 < width) (g : ℝ) :
    Envelope (vacuum R P m g) := by
  exact ((Envelope.const (g ^ 2 * P.poly m g)).mul
    (AllOrder.Laplace.toll_main (path_bounds (period := period) R m hm)).fit).add
    ((Envelope.const (radicand R P m g)).mul
      (ActualGradedVacuum.restored_envelope H hwidth (coupling R P m g)))

/-- Equality of the full vacuum functions on the original physical
coupling domain; every layer and the kinetic correction remain present. -/
theorem vacuum_matches {g : ℝ} (hg : 0 < g)
    (hb : 0 < (g ^ 2)⁻¹ + P.poly m g)
    (U : Config G (R.family.side m period)) :
    vacuum R P m g U = ActualProducedVacuumRestoration.vacuum P m g U := by
  let h := Currency.gain ((g ^ 2)⁻¹ + P.poly m g)
  have hh : h ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hb).ne'
  have hr : radicand R P m g = (g / h) ^ 2 :=
    (ActualProducedVacuumRestoration.model_ratio P m hg.ne' hb.le).symm
  have hc : radicand R P m g * h ^ 2 = g ^ 2 := by
    rw [hr]
    field_simp [hh]
  have hl : radicand R P m g * (h ^ 2 * unmaskedLayers (P.layers m) h U) =
      g ^ 2 * unmaskedLayers (P.layers m) h U := by
    rw [← mul_assoc, hc]
  rw [vacuum, coupling_eq_gain R P m hg hb,
    ActualGradedVacuum.restored_eq H hh, hl]
  unfold kinetic ActualProducedVacuumRestoration.vacuum
  dsimp only [h]
  ring

/-- The original no-flags action identity now uses this concrete analytic
vacuum. The native restriction and the separate loop term are unchanged. -/
theorem model_action {g : ℝ} (hg : 0 < g)
    (hb : 0 < (g ^ 2)⁻¹ + P.poly m g)
    (U : Config G (R.family.side m period))
    (hU : flags (R.family.path.levels.budget m).threshold U = ∅) :
    Integral.temperature g *
        (mainTerm (R.family.path.levels.params m).clip
          (R.family.path.rep N period m).path U + vacuum R P m g U) +
      Precision.loop (R.family.path.rep N period m).path U = modelAction P m g U := by
  rw [vacuum_matches R P m H hg hb U]
  exact ActualProducedVacuumRestoration.model_action P m hg.ne' U hU

theorem vacuum_receipts (hm : m ≤ N) (hwidth : 0 < width) :
    GradeAt 3 (Bulk.projected (vacuum R P m)) ∧
      (∀ g : ℝ, GaugeInvariant (vacuum R P m g)) ∧
      (∀ g : ℝ, Envelope (vacuum R P m g)) :=
  ⟨(vacuum_grade R P m H hm hwidth).lower (by decide),
    vacuum_gauge R P m H hm, vacuum_envelope R P m H hm hwidth⟩

end YM.Integration.ActualAnalyticPlanVacuum
end
