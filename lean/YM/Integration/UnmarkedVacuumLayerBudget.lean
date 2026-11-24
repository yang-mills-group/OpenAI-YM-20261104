import YM.Integration.QuadraticVacuumAnalytic
import YM.Integration.ActualRunRetunedVacuum

/-! Admission is stated on the actual retuned unmarked layer list. The
fixed schedule only needs to pay its real atoms at the next width; a larger
advertised geometry bound is absent from this criterion. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.UnmarkedVacuumLayerBudget

open Filter Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato Comparison.RG02
open IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped Classical Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
    (R : Run G) {J : Request V} {A : NumericSchedule R.family J}
    {d : LocalFormal.Datum R.family Γ} {caps : Handoff.OutputCapacities}
    {Y : Bulk.Chain R.family.path} {K : NumericPrices A} {F : AnalyticInput J A d}

/-- The fixed input width, budget, rank and norm pay the actual coefficient
representation of this selected output, including its covers and zero rows. -/
def Fits (M : AnalyticOutput caps Y K F) (m : ℕ) : Prop :=
  Nonempty (GradedVacuumLayers (ActualRunRetunedVacuum.retunedLayers R M)
    (A.inputNorm m) J.order J.vacuumRankCap (A.inputWidth m) (A.admittedCost m))

theorem retuned_quadratic (M : AnalyticOutput caps Y K F) (hJ : J.order = 2) :
    ActualRunRetunedVacuum.retunedLayers R M = [] := by
  have h := QuadraticVacuumAnalytic.selected_layers R J A d M hJ d.level d.below.le
  unfold ActualRunRetunedVacuum.retunedLayers
  rw [h]
  rfl

/-- At quadratic order the genuine receipt holds at every pair of levels
without any relation between input and output widths or costs. -/
theorem quadratic (M : AnalyticOutput caps Y K F) (hJ : J.order = 2) (m : ℕ) :
    Fits R M m := by
  unfold Fits
  rw [retuned_quadratic R M hJ]
  exact ⟨QuadraticVacuumAnalytic.empty_layers _ (A.inputNorm m) J.order J.vacuumRankCap
    (A.inputWidth m) (A.admittedCost m) (A.input_width_pos m) (A.admitted_cost_ge_one m)⟩

/-- Replace the input vacuum in an admitted chart by precisely the provided
analytic list. All of the unmasked and coupling-ray action is recovered
from its own priced atoms on this same original chart. -/
def input (F₀ : AnalyticInput J A d) (layers : List (Piece G (R.family.side (d.level+1) d.period)))
    (sl : Render.permits layers (A.inputNorm d.level))
    (H : GradedVacuumLayers layers (A.inputNorm d.level) J.order J.vacuumRankCap
      (A.inputWidth d.level) (A.admittedCost d.level)) : AnalyticInput J A d := by
  let n := R.family.side (d.level+1) d.period
  let W := fun _ : TestSpace J.tests =>
    { Bulk.Colors.noHole G n Γ with vac := ActualGradedVacuum.restored layers }
  let P := VacuumAuxiliaryInput.packets J.tests G n Γ
  have hz := (Bulk.Colors.no_hole G n Γ).1
  have hVac := ActualGradedVacuum.analytic_vacuum H (A.input_width_pos _)
  have hW : InputColors W P := {
    well := fun _ => ⟨hVac.1.lower (by decide), hz.suppose_mark, hVac.2.1,
      hz.gauges, hVac.2.2.1, hz.prices⟩
    vacuum := fun _ _ => rfl
    power := fun _ _ => rfl
    marks := fun x g _ U => by
      rw [VacuumAuxiliaryInput.read]
      simp [Integral.markedLog, Multi.lit, W, Bulk.Colors.noHole, Poly.send_zero] }
  exact { VacuumAuxiliaryInput.analytic F₀ with
    layers := layers
    layers_paid := sl
    vacuum := H
    colors := W
    convention := hW
    whole_input := Classical.choice (ActualLayerFineAction.whole_action R Γ J d H
      (A.input_width_pos _) W P hW (fun _ => rfl)) }

/-- The new analytic input retains the original fine roots and the true
chosen vacuum list. Its auxiliary inserted sources alone vanish. -/
theorem data (F₀ : AnalyticInput J A d) (layers : List (Piece G (R.family.side (d.level+1) d.period)))
    (sl : Render.permits layers (A.inputNorm d.level))
    (H : GradedVacuumLayers layers (A.inputNorm d.level) J.order J.vacuumRankCap
      (A.inputWidth d.level) (A.admittedCost d.level)) :
    (input R F₀ layers sl H).layers = layers ∧
      (input R F₀ layers sl H).packets = VacuumAuxiliaryInput.packets J.tests G _ Γ ∧
      (input R F₀ layers sl H).fineRoots = F₀.fineRoots := ⟨rfl, rfl, rfl⟩

end YM.Integration.UnmarkedVacuumLayerBudget
