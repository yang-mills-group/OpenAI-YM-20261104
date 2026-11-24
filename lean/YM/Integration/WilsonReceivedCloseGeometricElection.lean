import YM.Integration.WilsonReceivedCloseCoissuedFunding
import YM.Integration.WilsonThermometerDisplacedCourse
import YM.Integration.WilsonReportLampForecast

/-! Elect the local angular event and the moving-coordinate root prices on the same
original run that issues the close-window signed three-face course. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseGeometricElection
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
universe u

open WilsonCoeffUV WilsonCoeffUV.Bank WilsonMarkedIndependentPhysicalIntake
open WilsonVacuumPreResetFiniteHeatScale WilsonVacuumPreResetFiniteHeatTable
variable {G:Gauge} {φ:ℕ→ℕ}

open WilsonReceivedCloseCoissuedFunding

theorem original (cap : ℕ → ℕ) (mono : Monotone cap) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (C : VowsR.LawScroll G φ)
    (split : MintClock.splits ≤ φ)
    (external : ∀ (s : Sheet G) (M : MapPrices), Permitted C s (ThroughLaunch.raging s M))
    (U : ℕ → ℕ) (more : Prediction G) (credit : WilsonFundedWindowMenu.AllPrices (@more)) :

    ∃ (R:Run G) (T:Campaign R) (W:Campaign.Pillars R T),
      (∀j,cap j≤(R.metals.p.profile j).order) ∧ more R.kit ∧ WilsonReportingForestAngularReflection.posted R ∧
      WilsonReportLampForecast.Ready R.family.path.levels ∧ WilsonReceivedCloseFundedHeat.Quiet R ∧ StationInvoice R ∧
      WilsonWindowOriginalHardRadius.Booked R.kit ∧ WilsonWindowReportingPace.Slow R.kit ∧
      WilsonWindowOriginalRun.ArchivedInputs R.kit ∧ WilsonWindowFormalPurchase.Canonical U R.kit ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧
      Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      (∃ Θ v, (CustodyR.minted G).items R.alloy.post R.y R.w Θ R.family.path.levels ∧
        Campaign.Sky R T Θ v ∧ WilsonReportingAbsoluteInletLiveRun.PanelDates R ∧
        WilsonReportingAbsoluteInletFundedRun.Reported R Θ.price ∧ AllAnchors R Θ.price) ∧
      ∃ books ahead, ∃ house : Treehouse.VariableHouse R (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls)
        C books R.family.path.levels.clock.kernel.penalty ahead (stages R.metals.p),
        ∃ salary:WilsonReceivedCloseOriginalTuition.Funds hG φ R.kit,
        (∀ (f:Extraction.Order) (F:(Bel R.family.book).Hierarchy) (q span sh:ℕ) (H angleCap cap' tol:ℝ),
          0 ≤ angleCap → 0 ≤ cap' → 0 < tol →
          WilsonReceivedCloseElectedProgram.Heard R hG (roots hG R.metals.p R.metals.K)
            (rollTab hG R.metals R.rolls) books ahead (f:=f) (F:=F) q span sh H angleCap cap' tol) ∧
        (∀ (f:Extraction.Order) (F:(Bel R.family.book).Hierarchy) (q span sh:ℕ) (H angleCap cap' tol:ℝ),
          0 ≤ angleCap → 0 ≤ cap' → 0 < tol →
          WilsonReceivedCloseFoldedStationProgram.Heard R hG (roots hG R.metals.p R.metals.K)
            (rollTab hG R.metals R.rolls) books ahead (f:=f) (F:=F) q span sh H angleCap cap' tol) ∧
        WilsonReceivedCloseFundedFields.Curvature R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) C books ahead house salary.1 salary.2 ∧
        WilsonReceivedCloseNamedSourceElection.Named R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) C books ahead house salary.1 salary.2 ∧
        WilsonReceivedCloseFundedOrdinary.Folded R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) C books ahead house salary.1 salary.2 ∧
        Given R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) C books ahead house salary.1 salary.2 ∧
        WilsonReceivedClosePriorFunding.Prior R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) C books ahead house salary.1 salary.2 ∧
        WilsonPhysicalHistoryPriorAperture.Paid R.rolls (roots hG R.metals.p R.metals.K) φ R.alloy.delay := by
  let acoustic := @Together G (@WilsonThermometerDisplacedCourse.angular G) (@WilsonReportLampForecast.Eligible G)
  have ready : WilsonFundedWindowMenu.AllPrices (@acoustic) := fun s T=>
    joint (WilsonThermometerDisplacedCourse.prepaid G s T) (WilsonReportLampForecast.allPrices s T)
  let all := @Together G (@more) (@acoustic)
  have paid : WilsonFundedWindowMenu.AllPrices (@all) := fun s T=>joint (credit s T) (ready s T)
  obtain ⟨R,T,W,tall,⟨other,angular,rootsReady⟩,quiet,station,hard,slow,archive,formal,correlations,
    fund,citizen,logBook,sky,books,ahead,house,salary,three,covered,curvature,named,folded,entire,
    charged,protect⟩ := WilsonReceivedCloseCoissuedFunding.original.{u} cap mono hG hε C split external U (@all) paid
  exact ⟨R,T,W,tall,other,angular,rootsReady,quiet,station,hard,slow,archive,formal,correlations,
    fund,citizen,logBook,sky,books,ahead,house,salary,three,covered,curvature,named,folded,entire,charged,protect⟩

end YM.Integration.WilsonReceivedCloseGeometricElection
