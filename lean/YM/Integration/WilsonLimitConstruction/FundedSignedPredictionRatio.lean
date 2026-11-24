import YM.Integration.WilsonLimitConstruction.FundedCoverPredictionRatio
import YM.Integration.WilsonLimitConstruction.FundedExactKineticContact

/-! The native finite-contact bounds specialized to an exact signed model. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonLimitConstruction.FundedSignedPredictionRatio
open Function Filter Lattice Wilson RG Precision Exterior Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Comparison.RG02.Assembly
open MatchingLedger.Compass.Income Pert.Asymptotics
open PhysicalWilsonActionConvention
open scoped Topology ContDiff Classical BigOperators

theorem polynomial_small {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule T.family J) (K : NumericPrices A)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = m →
      ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
        (M : SignedAnalyticOutput caps Y K I),
      |M.plan.poly datum.level
          (regulatorRun T.family datum.cutoff datum.period (datum.level + 1))| *
        regulatorRun T.family datum.cutoff datum.period (datum.level + 1)^2 ≤ epsilon := by
  filter_upwards [FundedCoverPredictionRatio.polynomial_small T hG hT (R:=R) caps A K epsilon hepsilon] with m paid
  intro datum hm Y I M
  exact paid datum hm Y I (FundedPhysicalCatalogue.ofSigned M) (FundedExactKineticContact.tested T M hG _)

theorem predicted_fine {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule T.family J) (K : NumericPrices A) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = m →
      ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
        (M : SignedAnalyticOutput caps Y K I),
      0 < M.plan.predict datum.level ∧
      (1 / 2 : ℝ) ≤ Currency.gain (M.plan.predict datum.level) /
          regulatorRun T.family datum.cutoff datum.period (datum.level + 1) ∧
      Currency.gain (M.plan.predict datum.level) /
          regulatorRun T.family datum.cutoff datum.period (datum.level + 1) ≤ 2 := by
  filter_upwards [FundedCoverPredictionRatio.predicted_fine T hG hT (R:=R) caps A K] with m paid
  intro datum hm Y I M
  exact paid datum hm Y I (FundedPhysicalCatalogue.ofSigned M) (FundedExactKineticContact.tested T M hG _)

theorem actual_ratio {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule T.family J) (K : NumericPrices A) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = m →
      ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
        (M : SignedAnalyticOutput caps Y K I),
      0 < M.plan.predict datum.level ∧
      (1 / 4 : ℝ) ≤ Currency.gain (M.plan.predict datum.level) /
          regulatorRun T.family datum.cutoff datum.period datum.level ∧
      Currency.gain (M.plan.predict datum.level) /
          regulatorRun T.family datum.cutoff datum.period datum.level ≤ 4 := by
  filter_upwards [FundedCoverPredictionRatio.actual_ratio T hG hT (R:=R) caps A K] with m paid
  intro datum hm Y I M
  exact paid datum hm Y I (FundedPhysicalCatalogue.ofSigned M) (FundedExactKineticContact.tested T M hG _)

theorem stripe {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule T.family J) (K : NumericPrices A) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = m →
      ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
        (M : SignedAnalyticOutput caps Y K I),
      M.plan.predict datum.level ∈
        Currency.stripe (Currency.B T.family.path.levels datum.level) := by
  filter_upwards [FundedCoverPredictionRatio.stripe T hG hT (R:=R) caps A K] with m paid
  intro datum hm Y I M
  exact paid datum hm Y I (FundedPhysicalCatalogue.ofSigned M) (FundedExactKineticContact.tested T M hG _)

end YM.Integration.WilsonLimitConstruction.FundedSignedPredictionRatio
end
