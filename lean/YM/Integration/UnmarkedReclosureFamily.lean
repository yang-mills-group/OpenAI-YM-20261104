import YM.Integration.UnmarkedVacuumReentry
import YM.Integration.QuadraticVacuumHistory
import YM.Integration.ActualRunReadoutWidth
import YM.Integration.ActualRunShortHullsTail

/-! Uniform descent of the selected unmarked family on a single schedule.
The kinetic and regular charges are separate. The analytic layer bill is
asked only for the very model produced by the family on that actual state. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.UnmarkedReclosureFamily

open Filter Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato Comparison.RG02
open IterationFour IterationFour.Vacuum AnalyticBridge.VerifiedReset
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Canonical QuadraticVacuumHistory
open scoped Topology Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
    (R : Run G) {J : Request V} {A : NumericSchedule R.family J}
    {caps : Handoff.OutputCapacities} {η : ℕ → ℕ → ℕ → ℝ}

/-- The inherited cap is the native canonical reset invoice on each
eligible incoming state, before the cutoff and torus are chosen. -/
def Inherited (K : NumericPrices A) : Prop :=
  ∀ᶠ l : ℕ in atTop, ∀ (d : LocalFormal.Datum R.family Γ), d.level = l →
    ∀ (F : AnalyticInput J A d) (I : FullPreparedInputAt F (η d.cutoff d.period d.level)),
    ActualCanonicalInputPayload.errorPrice R I K ≤ J.inheritedConstant *
      Pert.Asymptotics.regulatorRun R.family d.cutoff d.period d.level ^
        ((J.order : ℝ) + 1 - J.eta)

/-- The flat cap is chosen once; the witness on each state renders its
actual kinetic discrepancy at the entire requested next input norm. -/
def Calibrations (K : NumericPrices A) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ (d : LocalFormal.Datum R.family Γ), d.level = m+1 →
    ∀ (Y : Bulk.Chain R.family.path) (F : AnalyticInput J A d)
      (I : FullPreparedInputAt F (η d.cutoff d.period d.level))
      (M : AnalyticOutput caps Y K F) (S : Retained.Chosen K I M) (P : CanonicalOutput S),
    I.carrier.rep.eval = (R.family.path.rep d.cutoff d.period (d.level+1)).eval →
    ∃ C : CalibrationPresentation P.output.carrier.rep (A.inputNorm m) (η d.cutoff d.period m),
      ∀ U, C.amount U =
        (P.output.carrier.rep.beta - R.family.path.β d.cutoff d.period d.level) *
        Push.BetaTransport.kinetic (R.family.path.rep d.cutoff d.period d.level).path
          (R.family.path.levels.params d.level).clip (A.inputNorm m) U

variable {Y : Bulk.Chain R.family.path} {floor n : ℕ → ℕ}
    {models : Retained.ModelFamily (R := Γ) caps Y J A floor n} (Φ : CompleteFamily models η)
local notation "Paid" => State R Γ J A η

/-- Only the fixed family's own selected models must fit the next chart.
Every atom and retained mask is part of the graded receipt. -/
def LayerCosts : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ (old : Paid), old.datum.level = m+1 →
    ∀ (hfirst : Φ.joint.first ≤ old.datum.level)
      (hfloors : Handoff.LocalFloors floor n old.datum)
      (hulls : Retained.ShortHulls models.prices old.datum),
    UnmarkedVacuumLayerBudget.Fits R
      (models.realize old.datum (Φ.joint.after_model.trans hfirst) hfloors hulls old.analytic) m

theorem quadratic (hJ : J.order = 2) : LayerCosts R Φ :=
  .of_forall fun m _ _ _ _ _ => UnmarkedVacuumLayerBudget.quadratic R _ hJ m

/-- All uniform thresholds precede the cutoff, torus, and original rough
state. The resulting edges retain the canonical reset and the actual retuned
layer list on the single chosen model family at every perturbative order. -/
theorem steps (hG : G.Simple) (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (horders : ∀ k, k ≤ (R.metals.p.profile k).order ∧ k ≤ (R.metals.p.profile k).power)
    (hwhole : ∀ v, ∃ k w : ℕ, J.tests v = ⟨.whole, k, w⟩) (hJ : SameNorm J)
    (hfloor : ∃ first : ℕ, ∀ d : LocalFormal.Datum R.family Γ, first ≤ d.level →
      Handoff.LocalFloors floor n d)
    (hInherited : Inherited R models.prices (Γ := Γ) (η := η))
    (hCal : Calibrations R models.prices (Γ := Γ) (caps := caps) (η := η))
    (hCost : LayerCosts R Φ) :
    Steps Φ := by
  obtain ⟨first, hfl⟩ := hfloor
  obtain ⟨hullFirst, hhull⟩ := ActualRunShortHullsTail.atRun R hG A models.prices
  have hg := (tendsto_add_atTop_nat 1).eventually
    (ActualRunReadoutWidth.eventually_geometry R hG hReadout J.outputFieldOrder
      J.outputDistanceOrder J.outputSupport J.field_minimum J.distance_minimum J.output_support_pos)
  filter_upwards [hg, (tendsto_add_atTop_nat 1).eventually hInherited, hCal, hCost,
    QuadraticVacuumAnalytic.eventually_input R J A horders hwhole (Γ := Γ),
    eventually_ge_atTop Φ.joint.first, eventually_ge_atTop first, eventually_ge_atTop hullFirst]
    with m hgeom hprice hcal hcost hinput hlate hfloorLevel hhullLevel
  intro old hm W field
  have hfirst : Φ.joint.first ≤ old.datum.level := by omega
  have hfloors := hfl old.datum (by omega)
  have hulls := hhull Γ old.datum (by omega)
  let M := models.realize old.datum (Φ.joint.after_model.trans hfirst) hfloors hulls old.analytic
  let S := Φ.joint.select old.datum hfirst hfloors hulls old.analytic old.prepared old.intake
  let P := Φ.canonical old.datum hfirst hfloors hulls old.analytic old.prepared old.intake
  have hOut := ActualRepeatedNorm.norm_unique R.family J.outputFieldOrder
    J.outputDistanceOrder J.outputSupport J.field_minimum J.distance_minimum
    J.output_support_pos (m+1) (A.outputNorm (m+1)) (A.output_norm (m+1))
  have hw : Geo.Width (A.outputNorm old.datum.level) (R.family.path.levels.params old.datum.level).clip
      (R.family.path.levels.params old.datum.level).width := by
    rw [hm, hOut]
    exact hgeom.2
  obtain ⟨C, hC⟩ := hcal old.datum hm Y old.analytic old.prepared M S P old.actual
  let d₁ := ActualNextLocalDatum.descend old.datum hm W field
  let region := cast (congrArg
    (fun k => Comparison.Density.Testing.Region (fun v => (J.tests v).Mood)
      (R.family.side k old.datum.period)) hm) M.region
  obtain ⟨F₀, _, _, hR, _⟩ := hinput d₁ rfl old.analytic.physical_period
    (ActualNextLocalDatum.fineRoots old.analytic hm) region
  obtain ⟨F₁, I₁, intake, hcar, hE, hCalStored, hB, hReg, hFor, hAct, hL, hP, _⟩ :=
    UnmarkedVacuumReentry.step R S P hG hJ hm W field F₀ hR
      (hcost old hm hfirst hfloors hulls) hw (hprice old.datum hm old.analytic old.prepared)
      C hC old.actual
  let next : Paid := { datum := d₁, analytic := F₁, prepared := I₁, intake := intake, actual := hAct }
  exact ⟨next, rfl, hfirst, hfloors, hulls, hcar, hE, hB, hReg, hFor, hL, hP, C, hCalStored, hC⟩

end YM.Integration.UnmarkedReclosureFamily
