import YM.Integration.WilsonLimitConstruction.FundedCoverCoefficientMass
import YM.Integration.WilsonLimitConstruction.FundedExactKineticContact

/-! The native finite-contact bounds specialized to an exact signed model. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonLimitConstruction.FundedSignedCoefficientMass
open Function Filter Lattice Wilson RG Precision Exterior Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Comparison.RG02.Assembly
open PhysicalWilsonActionConvention
open scoped Topology ContDiff Classical BigOperators

theorem coefficient_polynomial {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule T.family J) (K : NumericPrices A) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ᶠ m : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = m →
      ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
        (M : SignedAnalyticOutput caps Y K I) (_x : TestSpace J.tests) (e : ℕ),
      e ≤ J.order - 2 →
      |M.plan.coefficient datum.level e| ≤
        (C * (A.admittedCost m)^d) *
          FiniteCoefficientMass.mass (M.plan.coefficient datum.level) e ^ (J.order + 4) := by
  obtain ⟨C,hC,d,paid⟩ := FundedCoverCoefficientMass.coefficient_polynomial T hG hT (R:=R) caps A K
  refine ⟨C,hC,d,?_⟩
  filter_upwards [paid] with m bought
  intro datum hm Y I M x e he
  exact bought datum hm Y I (FundedPhysicalCatalogue.ofSigned M) x e he (FundedExactKineticContact.tested T M hG x)

theorem mass_polynomial {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule T.family J) (K : NumericPrices A) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ᶠ m : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = m →
      ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
        (M : SignedAnalyticOutput caps Y K I) (_x : TestSpace J.tests),
      1 + ∑ j ∈ Finset.range (J.order - 2 + 1), |M.plan.coefficient datum.level j| ≤
        C * (A.admittedCost m)^d := by
  obtain ⟨C,hC,d,paid⟩ := FundedCoverCoefficientMass.mass_polynomial T hG hT (R:=R) caps A K
  refine ⟨C,hC,d,?_⟩
  filter_upwards [paid] with m bought
  intro datum hm Y I M x
  exact bought datum hm Y I (FundedPhysicalCatalogue.ofSigned M) x (FundedExactKineticContact.tested T M hG x)

end YM.Integration.WilsonLimitConstruction.FundedSignedCoefficientMass
end
