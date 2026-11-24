import YM.Integration.WilsonOriginalBlissReflectedProgram
import YM.Integration.WilsonOriginalCourseSupplement

/-! The original Wilson hierarchy, its physical extraction and its common reflected MS source programme. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalBlissReflectedElection
universe u
open Filter Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl OPE.Therm
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Calibration RegulatorIR.FVAAlt2
open WilsonPositionProgramReporterBand
open XSpace XSpace.Cirrus FVA2 FVA2.Register MS MS.Land
open Extraction Extraction.Banks RG17 Spec Table
open scoped Classical ENNReal BigOperators
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
open WilsonEmittedOriginalSchool

variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
  {H:(Climb.Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}
  {arch:Trace.Terrace.Arch R.family}(bliss:Trace.Pilot.Bliss F l arch H)
  (J:ℝ→PhysMS.tower S)(level:ℝ→ℕ)(shift:∀d,ℝ→R.family.label d ≃ₗ[ℂ] R.family.label d)
  {T₀:Campaign R}{W:Campaign.Pillars R T₀}{simple:G.Simple}{ε:ℝ}
  (fund:WilsonLimitConstruction.FundedOriginalProperties.{u} simple ε W)
  (schedule:WilsonEmittedNestedGround.Schedule R)(slow:WilsonWindowReportingPace.Slow R.kit)

variable
  (root:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (seat:root.Tab R.rolls){ψ:ℕ→ℕ}(scroll:VowsR.LawScroll G ψ)
  (books:Mentor.Offices.Books root R.rolls seat ψ)(forecast:Mentor.Forecast root R.rolls seat ψ books)
  {ZΘ:ℝ}{profile:PhysicalNext.ThroughLaunch.Orders}
  (house:Treehouse.VariableHouse R root seat scroll books ZΘ forecast profile)
  (income:WilsonMovingMentorRootRadius.Income (M:=R.metals) root ψ R.alloy.delay)
  (active:∀j,MintClock.Employment root ψ j (R.rolls.L j))

def Frame :Prop:=
  ∀(level:ℝ→ℕ)(shift:∀d,ℝ→R.family.label d ≃ₗ[ℂ] R.family.label d)
    (AUX:Type)(axis:Axis)(dial:Bool)(L:XSpace.Run), ∃(Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
      (P:Prescription (Press.portDeck G)), Z.run=L ∧ ∃pair:Main.Match Z simple M P dial,
      WilsonSubcriticalOriginalProgram.Compared F J Z M ∧ ∃Q:Prescription (Press.portDeck G),
      ∃calibration:TaylorOKPl M (YM.FVAAlt2.Lobby.Table (Lodge.basisR R) (Press.portDeck G)) Q,
        WilsonOriginalBlissPositionProgram.Book R F bliss J level shift fund schedule slow AUX axis Z M Q calibration pair ∧
        WilsonOriginalBlissReflectedProgram.Withdrawn R (simple:=simple) root seat books forecast Q l
def Pinned (cohort:Ultrafilter (ℕ×ℕ)→Prop):Prop:=
  ∀v:Extraction.Order,∃(w:Extraction.Order)(S:Table R.family.book)(F:Spec.Final R.family (v.refine w) S)
    (L:EveryPhase.Almanac F)(reader:OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin),
    EveryPhase.Completed F L ∧ Trace.Target.Result.{u} F simple ∧ Trace.Target.Exclusion.{u} F ∧
    OPE.Facilities R.family (v.refine w) S ∧ OPE.Orbits.Foundation F reader ∧
    ∃(Y:(Bel R.family.book).Hierarchy)(arch:Trace.Terrace.Arch R.family)(l:Ultrafilter (ℕ×ℕ))
      (bliss:Trace.Pilot.Bliss F l arch Y)(J:ℝ→PhysMS.tower S)(P P':ℝ→Spin.change S 4)
      (χ:E4→ℝ)(a b e:ℝ→ℝ)(X:Scaling S),
      (∃V,Trace.Over.Scribe (v.refine w) X V arch F.sector l F.room.kernel Y) ∧
      (∀ᶠ r in Trace.Pilot.trail,J r 4=P' r) ∧ Trace.Target.XScheme F simple Y l P P' χ ∧
      Trace.Target.FieldComparison F Y arch P P' a b e ∧ PhysMS.Leading F J ∧
      (∀d,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F Y (J r) d) ∧
      Tendsto Prod.fst (l:Filter (ℕ×ℕ)) atTop ∧ Tendsto Prod.snd (l:Filter (ℕ×ℕ)) atTop ∧
      cohort l ∧ RG12.Observing R.family F.room.cutoff (l:Filter (ℕ×ℕ))
        (fun d k=>(arch.M d k).symm.toLinearMap.toContinuousLinearMap) ∧
      (∀(level:ℝ→ℕ)(shift:∀d,ℝ→R.family.label d≃ₗ[ℂ] R.family.label d)
        (d:ℕ)(r:ℝ),R.family.ref d≤level r → ∀ᶠ z:ℕ×ℕ in (l:Filter (ℕ×ℕ)),∀v:R.family.label d,
          Trace.Terrace.Cturn R.family d (level r) z.1 z.2
            (RG17.atRef (WilsonOriginalBlissObserved.layout F bliss J level shift) d r z v)=
            ((R.family.S.a (level r)^d:ℝ):ℂ) • shift d r v) ∧
      Frame R F bliss J fund schedule slow root seat books forecast

include house income active in
theorem pinned (cohort:Ultrafilter (ℕ×ℕ)→Prop) (old:WilsonEmittedPositionSchool.Pinned.{u} R simple cohort):
    Pinned R fund schedule slow root seat books forecast cohort:=by
  intro v
  obtain ⟨z,S,F,L,reader,phases,target,exc,facilities,foundation,Y,arch,l,bliss,J,P,P',χ,a,b,e,X,
    scribe,star,scheme,operators,lead,obedient,top,torus,prior,observer,coordinates⟩:=old v
  refine ⟨z,S,F,L,reader,phases,target,exc,facilities,foundation,Y,arch,l,bliss,J,P,P',χ,a,b,e,X,
    scribe,star,scheme,operators,lead,obedient,top,torus,prior,observer,coordinates,?_⟩
  intro level shift AUX axis dial geometry
  exact WilsonOriginalBlissReflectedProgram.original (AUX:=AUX) R F bliss J level shift fund schedule slow
    root seat scroll books forecast house income active axis lead dial geometry

theorem funded (more:Prediction G)(credit:WilsonFundedWindowMenu.AllPrices (@more))(cap U : ℕ → ℕ) (mono : Monotone cap) (hG : G.Simple) {ε : ℝ} (positive : 0 < ε) :
    let tube := tube G
    let φ := MintClock.splits
    let scroll := WilsonEmittedOriginalSchool.scroll G
    let split : MintClock.splits ≤ φ := le_rfl
    ∃ (R:Run G)(T:Campaign R)(W:Campaign.Pillars R T),
      ∃schedule:WilsonEmittedNestedGround.Schedule R,more R.kit ∧
      (∀j,cap j≤(R.metals.p.profile j).order) ∧
      FundedDictionaryPatchPrices.Covered (WilsonEmittedDictionary.program tube) R ∧
      WilsonNeutralPointForecast.Enrolled R.metals.p.kernel R.family.path.levels ∧
      WilsonNeutralPointWeakForecast.Enrolled R.metals.p.kernel R.family.path.levels ∧
      WilsonOlderFreshGraphCommonHouse.supply hG scroll split U R.kit ∧
      WilsonReportingForestAngularReflection.posted R ∧
      WilsonReportLampForecast.Ready R.family.path.levels ∧ WilsonReceivedCloseFundedHeat.Quiet R ∧ StationInvoice R ∧
      WilsonWindowOriginalHardRadius.Booked R.kit ∧ ∃slow:WilsonWindowReportingPace.Slow R.kit,
      WilsonWindowOriginalRun.ArchivedInputs R.kit ∧ WilsonWindowFormalPurchase.Canonical U R.kit ∧
      NativeFVAPlateau.Correlations R ∧ ∃fund:FundedOriginalProperties.{u} hG ε W,
      Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      (∃ Θ v, (CustodyR.minted G).items R.alloy.post R.y R.w Θ R.family.path.levels ∧
        Campaign.Sky R T Θ v ∧ WilsonReportingAbsoluteInletLiveRun.PanelDates R ∧
        WilsonReportingAbsoluteInletFundedRun.Reported R Θ.price ∧ AllAnchors R Θ.price) ∧
      ∃ books ahead, ∃ house : Treehouse.VariableHouse R (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls)
        scroll books R.family.path.levels.clock.kernel.penalty ahead (stages R.metals.p),
        ∃ salary:WilsonReceivedCloseOriginalTuition.Funds hG φ R.kit,
        (∀ (f:Extraction.Order) (F:(Bel R.family.book).Hierarchy) (q span sh:ℕ) (H angleCap cap' tol:ℝ),
          0 ≤ angleCap → 0 ≤ cap' → 0 < tol →
          WilsonReceivedCloseElectedProgram.Heard R hG (roots hG R.metals.p R.metals.K)
            (rollTab hG R.metals R.rolls) books ahead (f:=f) (F:=F) q span sh H angleCap cap' tol) ∧
        (∀ (f:Extraction.Order) (F:(Bel R.family.book).Hierarchy) (q span sh:ℕ) (H angleCap cap' tol:ℝ),
          0 ≤ angleCap → 0 ≤ cap' → 0 < tol →
          WilsonReceivedCloseFoldedStationProgram.Heard R hG (roots hG R.metals.p R.metals.K)
            (rollTab hG R.metals R.rolls) books ahead (f:=f) (F:=F) q span sh H angleCap cap' tol) ∧
        WilsonReceivedCloseFundedFields.Curvature R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) scroll books ahead house salary.1 salary.2 ∧
        WilsonReceivedCloseNamedSourceElection.Named R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) scroll books ahead house salary.1 salary.2 ∧
        WilsonReceivedCloseFundedOrdinary.Folded R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) scroll books ahead house salary.1 salary.2 ∧
        Given R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) scroll books ahead house salary.1 salary.2 ∧
        WilsonReceivedClosePriorFunding.Prior R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) scroll books ahead house salary.1 salary.2 ∧
        WilsonReceivedCloseQGeometricFunding.Recorded R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) scroll books ahead house salary.1 salary.2 ∧
        WilsonReceivedCloseQNullFunding.Recorded R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) scroll books ahead house salary.1 salary.2 ∧
        WilsonReceivedCloseQUnitFunding.Recorded R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) scroll books ahead house salary.1 salary.2 ∧
        WilsonReceivedCloseQNamedTerminalFunding.Recorded R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) scroll books ahead house salary.1 salary.2 ∧
        WilsonPhysicalHistoryPriorAperture.Paid R.rolls (roots hG R.metals.p R.metals.K) φ R.alloy.delay ∧
        Pinned.{u} R fund schedule slow (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) books ahead (WilsonOriginalBlissQPost.Booked R hG (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls) scroll books ahead house salary.1 salary.2)  :=by
  intro tube φ scroll split
  obtain ⟨R,T,W,⟨schedule,extra⟩,tall,dictionary,strong,weak,school,gate,lamp,quiet,station,hard,slow,archive,formal,
    correlations,fund,citizen,logBook,sky,books,ahead,house,salary,three,covered,curvature,named,folded,
    charged,prior,geometric,null,unit,terminal,protect,old⟩:=
      WilsonEmittedPositionSchool.withSupplement more credit cap U mono hG positive
  refine ⟨R,T,W,schedule,extra,tall,dictionary,strong,weak,school,gate,lamp,quiet,station,hard,slow,archive,formal,
    correlations,fund,citizen,logBook,sky,books,ahead,house,salary,three,covered,curvature,named,folded,
    charged,prior,geometric,null,unit,terminal,protect,?_⟩
  exact pinned R fund schedule slow _ _ scroll books ahead house salary.1 salary.2 _ old

end YM.Integration.WilsonOriginalBlissReflectedElection
