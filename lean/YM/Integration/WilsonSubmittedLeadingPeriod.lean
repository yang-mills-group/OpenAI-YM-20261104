import YM.Integration.WilsonSubmittedPeriodSeam
import YM.Integration.WilsonVacuumPreResetFiniteHeatOriginal

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSubmittedLeadingPeriod
open Function Filter Lattice RG WilsonLimitConstruction Next.Foundations PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Bank
open WilsonSubmittedPeriodSeam (Bill)
open scoped BigOperators Classical Topology
variable {G:Gauge}

/-- The two leading enrolled degrees share the same forest-independent choice
of Wilson campaign and can be read at every later original finite appointment. -/
theorem original.{u} (simple:G.Simple){ε:ℝ}(hε:0<ε)
    (P:FundedCompanySelection.Prediction G)(hP:FundedPredictionSupply.AllPrices (@P)):
    ∃(R:Run G)(T:Campaign R)(W:Campaign.Pillars R T)(D₀ D₁:ℕ),
      P R.kit ∧ NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} simple ε W ∧
      ∀ᶠj:ℕ in atTop,Bill R 0 D₀ j ∧ Bill R 1 D₁ j:=by
  obtain ⟨v₀,D₀,zero⟩:=WilsonSubmittedPeriodSeam.original G 0
  obtain ⟨v₁,D₁,one⟩:=WilsonSubmittedPeriodSeam.original G 1
  let both:=@FundedPredictionSupply.Both G (@FundedMarkedCoverRows.prices G v₁) (@P)
  have ready:FundedPredictionSupply.AllPrices (@both):=fun S k=>
    FundedPredictionSupply.both (FundedMarkedCoverRows.purchase v₁ S k) (hP S k)
  obtain ⟨R,T,W,first,rest,plateau,actual⟩:=
    FundedMarkedCoverRows.original.{u} simple hε v₀ (@both) ready
  refine ⟨R,T,W,D₀,D₁,rest.2,plateau,actual,?_⟩
  exact (zero R simple actual.2.2.2.2.2.2.1 first).and (one R simple actual.2.2.2.2.2.2.1 rest.1)

end YM.Integration.WilsonSubmittedLeadingPeriod
end
