import YM.Integration.WilsonPointChildTestSchool
import YM.Integration.WilsonPointChildWindingHierarchy

/-! Keep the complete original joint enrollment together with the full
    pretest budget on all pinned-cutoff sources, before either regulator. -/
noncomputable section
universe u
namespace YM.Integration.WilsonPointChildWindingSchool
open WilsonLimitConstruction OPE.Therm Further.PhysicalPeriodLimitF933
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra
open QuadraticLocal.Rebirth ConnectedActivityE6 FullQLocal FullQLocal.RenderedStep
open Multi Exterior WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open private staff from YM.Integration.WilsonOriginalClubSourcePackets
open Source Labels LocalComparison ComparisonDensity.Address Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonMixedPassportVote
open Pert.Asymptotics Extra.Histories WilsonOriginalReceivedChain
open scoped Classical BigOperators
open VowsR QuadraticLocal.Affinity Sycamore
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler
open PhysicalNext.Repeat.Daisy.Charity.RG12
open ThroughLaunch AllOrder AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowRootPurchase WilsonWindowJointPurchase WilsonWindowBookPurchase WilsonWindowUniversalSchool
open WilsonReportingAbsoluteInletSimultaneous
open scoped Classical
open FVA1 Extraction Table Climb

open WilsonCoeffUV WilsonCoeffUV.Bank WilsonMarkedIndependentPhysicalIntake
open WilsonVacuumPreResetFiniteHeatScale WilsonVacuumPreResetFiniteHeatTable
open WilsonReceivedCloseCoissuedFunding
variable {G:Gauge}

noncomputable def fare (G:Gauge):ℕ → Gear G → ℝ := (WilsonPointChildWindingHierarchy.original G).choose

def Paid:Prediction G:=@FundedMarkedCoverRows.prices G (fare G)

theorem prepaid:WilsonFundedWindowMenu.AllPrices (@Paid G):=fun s M=>WilsonFundedWindowMenu.from_guard
  (WilsonFundedWindowCompany.of_prepaid (FundedMarkedCoverRows.purchase (fare G) s M))

theorem on_run (R:Run G)(simple:G.Simple)(reading:RG05Preconstruction.ReadoutPurchase R.b)
    (paid:Paid R.kit)(floor:WilsonPointChildFiledTest.Filed R)
    (strong:WilsonNeutralPointForecast.Filed R.kit)(weak:WilsonNeutralPointWeakForecast.Filed R.kit)
    {U:ℕ → ℕ}(formal:WilsonWindowFormalPurchase.Canonical U R.kit):WilsonPointChildWindingHierarchy.Filed R:=
  (WilsonPointChildWindingHierarchy.original G).choose_spec R simple reading paid floor strong weak U formal

theorem original (tube:Comparison.Density.Transport.LinkTube G)(cap:ℕ→ℕ)(mono:Monotone cap)
    (hG:G.Simple){ε:ℝ}(hε:0<ε){φ:ℕ→ℕ}(scroll:VowsR.LawScroll G φ)
    (split:MintClock.splits≤φ)
    (external:∀ (s:Sheet G)(M:MapPrices),Permitted scroll s (ThroughLaunch.raging s M))
    (U:ℕ→ℕ)(more:Prediction G)(credit:WilsonFundedWindowMenu.AllPrices (@more)) :
    ∃ (R:Run G)(T:Campaign R)(W:Campaign.Pillars R T),
      FundedOriginalProperties.{u} hG ε W ∧ more R.kit ∧ Paid R.kit ∧
      WilsonOlderFreshGraphCommonHouse.supply hG scroll split U R.kit ∧
      (∀j,cap j≤(R.metals.p.profile j).order) ∧
      FundedDictionaryPatchPrices.Covered (WilsonEmittedDictionary.program tube) R ∧
      WilsonPointChildFiledTest.Filed R ∧ WilsonPointChildWindingHierarchy.Filed R:=by
  obtain ⟨R,T,W,cut,grade,dictionary,strong,weak,house,common,_reflection,_ready,_quiet,_station,_hard,_slow,_archive,formal,_correlations,facts,_other⟩:=
    WilsonPointChildTestSchool.original.{u} tube cap mono hG hε scroll split external U (Together (@Paid G) (@more))
      (fun s M=>joint (prepaid s M) (credit s M))
  exact ⟨R,T,W,facts,common.2,common.1,house,grade,dictionary,cut,
    on_run R hG facts.2.2.2.2.2.2.1 common.1 cut strong weak formal⟩

end YM.Integration.WilsonPointChildWindingSchool
end
