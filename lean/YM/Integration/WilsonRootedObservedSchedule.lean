import YM.Integration.WilsonRootedObservedRate

/-! Evaluate the measured high-sector theorem on the numeric schedule's
own physical threshold and complete derivative and distance budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedObservedRate
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy MergeProof LocalLTE RGLocalTaylor
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Marker.Census V}
    {R : Run G} {J : Request V} {A : NumericSchedule R.family J}
    {d : LocalFormal.Datum R.family Γ} {F : AnalyticInput J A d} {η : ℝ}
    (I : FullPreparedInputAt F η) {book : Booking G} (H : WilsonRootedSubmittedTail.CashAt I book)

theorem scheduled {price : ℝ} (paid : Observed I H price)
    (base x : IndependentTests J.tests) (E : Finset ℕ) (K : Finset (ℕ×ℕ)) :
    let lev := R.alloy.B.a
    let Q := R.kit.target (lev.clock.J (d.level+1)) (lev.clock.J d.level)
    let M := (ManuscriptQLocalMarkedRoster.promised
      (ManuscriptQLocalMarkedHeightRun.rosterBudget I) base x E K).terms
    ManuscriptQLocalObservedComponents.Tested H Chi.canonical M (A.outputNorm d.level) F.inputRadii
      (ManuscriptQLocalMarkedHeightTail.matrix H M)
      (fun z => Height.tiredN H (ManuscriptQLocalMarkedHeightRun.length J) z.1)
      (expense J Q).earn price :=
  paid (A.outputNorm d.level) (A.output_norm d.level).threshold
    (A.output_norm d.level).order.le (A.output_norm d.level).distance.le base x E K

end YM.Integration.WilsonRootedObservedRate
end
