import YM.Integration.WilsonEmittedNestedGround
import YM.Integration.WilsonReceivedClosePriorFunding

/-! Retain the selected factorial calendar through the original source
purchases. Each theorem has the original specification on its one enrolled
run, whose block lengths and post-length invoice are retained alongside it. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u

namespace YM.Integration.WilsonReportingAbsoluteInletPrior
open Function Lattice RG Wilson RG.Supply Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowRootPurchase WilsonWindowJointPurchase WilsonFundedWindowMenu
open WilsonReportingAbsoluteInletSimultaneous
variable {G : Gauge}

theorem scheduled (cap : ℕ → ℕ) (mono : Monotone cap) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (φ : ℕ → ℕ) (p : Prediction G) (paid : AllPrices (@p)) :
    WilsonEmittedNestedGround.Enrolled (WilsonReportingAbsoluteInletPrior.original.{u} cap mono hG hε φ (@p) paid) := by
  obtain ⟨R,T,W,calendar,tall,⟨other,bill⟩,station,continuum,original,slow,table⟩ :=
    WilsonEmittedNestedGround.original.{u} cap mono hG hε
      (@Together G (@p) (@Menu G hG φ)) (fun s M => joint (paid s M) (credit hG φ s M))
  exact ⟨R,T,W,calendar,tall,other,station,on_run hG φ R bill,continuum,original,slow,table⟩

end YM.Integration.WilsonReportingAbsoluteInletPrior

namespace YM.Integration.WilsonReportingAbsoluteInletPhysicalSchool
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler
open PhysicalNext.Repeat.Daisy.Charity.RG12
open ThroughLaunch AllOrder AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowRootPurchase WilsonWindowJointPurchase WilsonWindowBookPurchase WilsonWindowUniversalSchool
open WilsonReportingAbsoluteInletSimultaneous
open scoped Classical
variable {G : Gauge} {φ : ℕ → ℕ}

theorem scheduled (cap : ℕ → ℕ) (mono : Monotone cap) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (C : VowsR.LawScroll G φ)
    (split : MintClock.splits ≤ φ)
    (external : ∀ (s : Sheet G) (M : MapPrices), Permitted C s (ThroughLaunch.raging s M))
    (U : ℕ → ℕ) (more : Prediction G) (credit : WilsonFundedWindowMenu.AllPrices (@more)) :
    WilsonEmittedNestedGround.Enrolled (WilsonReportingAbsoluteInletPhysicalSchool.original.{u} cap mono hG hε C split external U (@more) credit) := by
  let law := Tracks.vine (flow C) split
  let p : Prediction G := @Together G (@Together G (@more) (@WilsonWindowOriginalHardRadius.Booked G))
    (@Together G (@WilsonReportColumnSubsidy.Eligible G) (@WilsonWindowSchoolInvoice.grant G φ hG law U))
  have school := WilsonWindowSchoolInvoice.prepaid hG law U
    (fun s M => WilsonWindowCourseLaws.physical_course split (external s M))
  have paid : WilsonFundedWindowMenu.AllPrices (@p) := fun s M =>
    joint (joint (credit s M) (WilsonWindowOriginalHardRadius.allPrices s M)) (joint (WilsonReportColumnSubsidy.allPrices s M) (school s M))
  obtain ⟨R,T,W,calendar,tall,⟨⟨outside,hard⟩,subsidy,booked⟩,station,aperture,correlations,original,_,Θ,v,custody,sky,dates,report,anchors⟩ :=
    WilsonReportingAbsoluteInletPrior.scheduled.{u} cap mono hG hε φ (@p) paid
  obtain ⟨⟨B,chamber⟩,admit,pace,archive,formal⟩ := WilsonWindowSchoolInvoice.on_run hG R law U booked
  obtain ⟨F,house_paid⟩ := house hG R _ _ C B split chamber admit
  obtain ⟨citizen,logBook⟩ := WilsonReportCitizenRun.on_run.{u} hG W original subsidy
  exact ⟨R,T,W,calendar,tall,outside,station,hard,⟨B,F,house_paid⟩,aperture,pace,archive,formal,correlations,
    original,citizen,logBook,Θ,v,custody,sky,dates,report,anchors⟩

end YM.Integration.WilsonReportingAbsoluteInletPhysicalSchool

namespace YM.Integration.WilsonReceivedCloseSchoolElection
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler
open PhysicalNext.Repeat.Daisy.Charity.RG12
open ThroughLaunch AllOrder AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowRootPurchase WilsonWindowJointPurchase WilsonWindowBookPurchase WilsonWindowUniversalSchool
open WilsonReportingAbsoluteInletSimultaneous
open scoped Classical
variable {G : Gauge} {φ : ℕ → ℕ}

theorem scheduled (cap : ℕ → ℕ) (mono : Monotone cap) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (C : VowsR.LawScroll G φ)
    (split : MintClock.splits ≤ φ)
    (external : ∀ (s : Sheet G) (M : MapPrices), Permitted C s (ThroughLaunch.raging s M))
    (U : ℕ → ℕ) (more : Prediction G) (credit : WilsonFundedWindowMenu.AllPrices (@more)) :
    WilsonEmittedNestedGround.Enrolled (WilsonReceivedCloseSchoolElection.original.{u} cap mono hG hε C split external U (@more) credit) := by
  let tuition := @WilsonReceivedCloseOriginalTuition.Funds G hG φ
  have enrolled : WilsonFundedWindowMenu.AllPrices (@Together G (@more) tuition) :=
    fun s M => joint (credit s M) (WilsonReceivedCloseOriginalTuition.prepaid hG φ split s M)
  obtain ⟨R,T,W,calendar,tall,⟨entered,source⟩,receipts⟩ :=
    WilsonReportingAbsoluteInletPhysicalSchool.scheduled.{u} cap mono hG hε C split external U
      (@Together G (@more) tuition) enrolled
  exact ⟨R,T,W,calendar,tall,entered,source,receipts⟩

end YM.Integration.WilsonReceivedCloseSchoolElection

namespace YM.Integration.WilsonReceivedClosePriorFunding
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
variable {G:Gauge} {φ:ℕ→ℕ}

theorem scheduled (cap : ℕ → ℕ) (mono : Monotone cap) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (C : VowsR.LawScroll G φ)
    (split : MintClock.splits ≤ φ)
    (external : ∀ (s : Sheet G) (M : MapPrices), Permitted C s (ThroughLaunch.raging s M))
    (U : ℕ → ℕ) (more : Prediction G) (credit : WilsonFundedWindowMenu.AllPrices (@more)) :
    WilsonEmittedNestedGround.Enrolled (WilsonReceivedClosePriorFunding.original.{u} cap mono hG hε C split external U (@more) credit) := by
  obtain ⟨v,heat⟩:=WilsonVacuumPreResetFiniteHeatHierarchy.original G
  have fundedHeat:WilsonFundedWindowMenu.AllPrices (@FundedMarkedCoverRows.prices G v) := fun s T =>
    WilsonFundedWindowMenu.from_guard (WilsonFundedWindowCompany.of_prepaid (FundedMarkedCoverRows.purchase v s T))
  let both := @Together G (@more) (@FundedMarkedCoverRows.prices G v)
  have paired:WilsonFundedWindowMenu.AllPrices (@both) := fun s T=>joint (credit s T) (fundedHeat s T)
  obtain ⟨R,T,W,calendar,tall,⟨extra,gear⟩,salary,station,hard,⟨books,ahead,house⟩,protect,slow,archive,formal,correlations,
    fund,citizen,logBook,sky⟩:=WilsonReceivedCloseSchoolElection.scheduled.{u} cap mono hG hε C split external U
      (@both) paired
  let three (f:Extraction.Order) (F:(Bel R.family.book).Hierarchy) (q span sh:ℕ) (H angleCap maxSpan tol:ℝ)
      (hp : 0 ≤ angleCap) (cp : 0 ≤ maxSpan) (ep : 0 < tol) :=
    WilsonReceivedCloseElectedProgram.original R hG (roots hG R.metals.p R.metals.K)
      (rollTab hG R.metals R.rolls) C books ahead house (f:=f) (F:=F) fund slow protect salary.1 salary.2
      q span sh H angleCap maxSpan tol hp cp ep
  have named : WilsonReceivedCloseNamedSourceElection.Named R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) C books ahead house salary.1 salary.2 := WilsonReceivedCloseNamedSourceElection.named R hG (roots hG R.metals.p R.metals.K)
    (rollTab hG R.metals R.rolls) C books ahead house salary.1 salary.2 protect
  have ordinary : WilsonReceivedCloseFundedOrdinary.Folded R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) C books ahead house salary.1 salary.2 := WilsonReceivedCloseFundedOrdinary.folded R hG (roots hG R.metals.p R.metals.K)
    (rollTab hG R.metals R.rolls) C books ahead house salary.1 salary.2 named
  have charged : Prior R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) C books ahead house salary.1 salary.2 := prior R hG (roots hG R.metals.p R.metals.K)
    (rollTab hG R.metals R.rolls) C books ahead house salary.1 salary.2 protect
  have curvature : WilsonReceivedCloseFundedFields.Curvature R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) C books ahead house salary.1 salary.2 := WilsonReceivedCloseFundedFields.curvature R hG (roots hG R.metals.p R.metals.K)
    (rollTab hG R.metals R.rolls) C books ahead house salary.1 salary.2 protect
  refine ⟨R,T,W,calendar,tall,extra,heat R hG fund.2.2.2.2.2.2.1 gear,station,hard,slow,archive,formal,correlations,
    fund,citizen,logBook,sky,books,ahead,house,salary,three,?_,curvature,named,ordinary,charged,protect⟩
  intro f F q span degree H angleCap maxSpan tol hp cp ep
  exact WilsonReceivedCloseFoldedStationProgram.on_course R hG (roots hG R.metals.p R.metals.K)
    (rollTab hG R.metals R.rolls) C books ahead house q span degree H angleCap maxSpan tol hp ep
    (three f F q span degree H angleCap maxSpan (tol/2) hp cp (half_pos ep))

end YM.Integration.WilsonReceivedClosePriorFunding
