import YM.Integration.ActualWilsonForcedSlots
import YM.Integration.ActualWilsonResidualCoefficient
import YM.Integration.SelectedCofactorSupportBudget

/-! A native priced original Wilson coefficient for the signed retained
singleton, with its full change of spectator cofactors on every field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.Integration.ActualWilsonSingletonReentry

open Function Set Finset Lattice Wilson RG Marker Source Labels RG3.Script.Picnic RG3.Forms
open Comparison.RG02 LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Extra.Histories Relay Bid Planned.GuardedAtom Trace.Physical Trace.Physical.GermGraph PhysicalNext.Repeat.Legato
open SelectedCofactorCancellation
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} (R : Run G) (hG : G.Simple)
    {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {J : Request V}
    {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta}
    {M : AnalyticOutput caps Y K F} {delta : ℝ} {forcedOrder : ℕ}

/-- The represented fixed-run coefficient carries every physical marked
amplitude at the paid support price. The displayed difference is the full
change of the unnormalized pinned vacuum minors on the selected field. -/
theorem selected (S : Chosen K I M) (H : Bounds S delta forcedOrder) (v : V)
    (hreserve : (R.family.path.levels.budget datum.level).supportExponent ≤ J.outputSupport)
    (ho : F.coarseRoots v = 0)
    (hFine : I.carrier.rep.eval =
      (R.family.path.rep datum.cutoff datum.period (datum.level+1)).eval)
    (x : IndependentTests J.tests) :
    let C := R.family
    let N := datum.cutoff
    let p := datum.period
    let i := datum.level
    let d := J.outputWeight v
    let X := S.output.carrier
    let W := C.path.rep N p i
    let D := S.output.residual.leaf (testInclusion J.tests x)
    let e := ActualWilsonForcedSlots.address X.rep (OriginalForcedAddresses.actual_keeper R hG N i p datum.below.le)
    let g := Pert.Asymptotics.regulatorRun C N p (i+1)
    let r := F.kernelCosts v * g^forcedOrder / F.outputRadii v
    ∃ q : store C d p i,
      q.x = 0 ∧ q.regular = 0 ∧
      (∀ j U, q.forced j U = (D.contents.each j U).part (B.fire v)) ∧
      q.Format 0 C.params X.rep ∧ q.remBound 0 X.rep (safety C i) r ∧
      let b := ActualWilsonForcedSlots.original R hG datum.below.le X q
      reads d N p i b r ∧ b.x = 0 ∧ b.regular = 0 ∧
      (∀ j U, b.forced (e j) U = (D.contents.each j U).part (B.fire v)) ∧
      (∀ k, k ∉ Set.range e → b.forced k = 0) ∧
      ∀ U, q.density 0 (C.localSection d) X.rep U - value d N p i b U =
        (Real.exp (X.rep.exponent U) : ℂ) *
          (∑' s, ∑ j ∈ s, (D.contents.each j U).part (B.fire v) * pinnedVacuum X.rep U j s) -
        (Real.exp (W.exponent U) : ℂ) *
          ∑' s, ∑ j ∈ s, b.forced j U * pinnedVacuum W U j s := by
  intro C N p i d X W D e g r
  obtain ⟨q,hx,hr,hq,hform,hprice⟩ := ActualWilsonResidualCoefficient.selected S H v hreserve x
  have hrow (j : ℕ) (U : Config G (C.side i p)) :
      q.forced j U = (D.contents.each j U).part (B.fire v) := by
    rw [hq]
    exact (ActualWilsonForcedRow.each_solution D v j U
      (SelectedCofactorSupportBudget.tagged_summable H.residual_price F.kernel_positive x j U)).symm
  rw [ho] at hform hprice
  have hbook := ActualWilsonForcedSlots.original_price R hG datum.below.le X q hform hprice
  have he := S.output.output_vacuum R.makes datum.below hFine
  refine ⟨q,hx,hr,hrow,hform,hprice,hbook.1,hx,hr,?_,?_,?_⟩
  · intro j U
    change (ActualWilsonForcedSlots.place X.rep _ q).forced (ActualWilsonForcedSlots.address X.rep _ j) U = _
    rw [ActualWilsonForcedSlots.on_slot, hrow]
  · exact fun _ hk => ActualWilsonForcedSlots.off_slot _ q hk
  intro U
  have hdiff := ActualWilsonForcedSlots.original_difference R hG datum.below.le X q he U
  simpa only [ActualWilsonForcedGraph.gas_pinned, hrow] using hdiff

end YM.Integration.ActualWilsonSingletonReentry
