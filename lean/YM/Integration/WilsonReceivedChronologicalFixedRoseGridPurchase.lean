import YM.Integration.WilsonReceivedChronologicalFixedRoseGridFolio
import YM.Integration.WilsonReceivedChronologicalFixedRoseGridCampus
import YM.Integration.WilsonReceivedChronologicalFixedRoseGridField
import YM.Integration.WilsonReceivedChronologicalFixedRoseOriginalCell
import YM.Integration.WilsonReceivedChronologicalFixedRoseVariation
import YM.Integration.WilsonReceivedChronologicalFixedRoseTestSource
import YM.Integration.WilsonReceivedChronologicalFixedRoseOriginalEnds
import YM.Integration.WilsonReceivedChronologicalFixedRoseOriginalAccount
import YM.Integration.WilsonReceivedChronologicalFixedRoseBothFees
import YM.Integration.WilsonReceivedChronologicalFixedRoseCurrentFee
import YM.Integration.WilsonAddressedPublicFirstRoseBoundary
/-! Both endpoints of one fitted physical Rose have actual funded returns at the
same panel, with its original earlier law and one deposited stencil salary. -/
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseGridPurchase
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Embroider WilsonOriginalCollarTeacher WilsonOriginalAllOrderCalendar WilsonOriginalAllOrderCourse
open WilsonOriginalOpticalSchedule WilsonIndependentCollarCensusCourse WilsonOriginalCollarElection
open WilsonReceivedFixedDigitHistory WilsonReceivedCanonicalVerseBasis WilsonThermometerDeclaredSeeds
open FundedMarkedPathSelection WilsonIndependentCollarAddressedSource Comparison.Density.Transport Pert.Asymptotics
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV QuadraticLocal QuadraticLocal.Mentor
open scoped Classical BigOperators Topology
open Marker Multi QuadraticLocal QuadraticLocal.Earn
open WilsonOriginalCensusDatedSchools (Paired)
open WilsonOriginalCensusMeasuredStation (CreditAt)
open WilsonCoeffUV.Bank.Carp
open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusFundedAttendance
open WilsonOriginalCensusAttendanceStation WilsonOriginalCensusPublicationClock
open Function Filter Finset Lattice RG RG.Supply Org PhysicalNext.Repeat Legato
open Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open AllOrder AllOrder.Floe QuadraticLocal QuadraticLocal.Rebirth QuadraticLocal.Sunrise.Aviary
open AllOrder.Transit AllOrder.Transit.WheelP
open WilsonOlderFreshGraphAward WilsonThermometerDeclaredSeeds
open WilsonOriginalMeasuredOccupiedForest (Read)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetDepositedGeometric WilsonOriginalOccupiedForestIntegral
open WilsonMarkedKineticDefect WilsonMarkedKineticGerm
open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusAttendanceStation
open WilsonMarkedIndependentPhysicalIntake
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetOriginalOutput Marker Multi
open WilsonVacuumPreResetTorusDeposit (bank)
open WilsonVacuumPreResetTorusGrade (evaluated)
open FVA1Physical.TwoReset (MassCall)
open AllOrder.Floe.Step
open AllOrder.Ker Primitives.TwoWave.RealSlice
open WilsonVacuumPreResetDatedDeposit (Issued)
open FVA1Physical.TwoReset (AffineMass)
open PertExtension.Series PowerSeries
open AllOrder AllOrder.Floe
open AllOrder.Floe.Step.PlanV FVA1Physical.TwoReset
open WilsonVacuumPreResetDatedCourse (coin)
open Primitives.TwoWave.RealSlice
open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonOriginalOccupiedForestIntegral (numerator)
open Next.SectorChange MeasureTheory
open WilsonOriginalCensusFiledAttendance (QuietAt)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedCanonicalVerseBasis OriginalMarkedSourceComet
open Multi WilsonCoeffUV.Blue
open WilsonReceivedChronologicalFixedReserve (terms charges)
open WilsonReceivedChronologicalFixedEarner (programme start)
open WilsonReceivedChronologicalFixedEnrollment (Cohort)
open WilsonReceivedChronologicalFixedTariff (gross allowance)
open WilsonOriginalCensusFaceAdmission (housed)
open WilsonReceivedChronologicalMaterialLine (homes)
open WilsonReceivedChronologicalMaterialApertures (spread diameter)
open WilsonOriginalCensusDatedPeriodOpening (Opened)
open WilsonOriginalCensusDatedHeldTariff (Rates)
open WilsonOriginalFixedTestCensusPublicBase (base)
open WilsonOriginalCensusPublicationClock (Open)
open WilsonCenteredPhysicalPanel
open StressFlux.Matching Next.UVStress
open WilsonReceivedChronologicalFixedPlaced (Purchased)
open WilsonReceivedChronologicalFixedPorts (Period)
open WilsonReceivedCanonicalSocketSeed (contact)
open WilsonAddressedPublicSubmittedDates (grades positive)
open WilsonAddressedPublicFirstPeriod (appointment)
open WilsonAddressedPublicFirstRoseCampus (seller financed)
open WilsonAddressedPublicFirstRoseOffer (Sold)
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators

open WilsonOriginalCensusCanonicalRows WilsonOriginalMixedBlockRows WilsonThermometerDeclaredSeeds
open WilsonOriginalStarSceneWords (rank)
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider OriginalMarkedSourceComet
open Filter MintClock XSpace Pert.Asymptotics

open WilsonVacuumPreResetStationaryChange (step coarse levels)
open WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalMeasuredOccupiedForest (Read)
open WilsonOriginalRawQReversion (coordinates)
open WilsonOriginalCensusCanonicalTopCopies (origins)
open WilsonOriginalCensusCanonicalPageFold (folded)
open WilsonReceivedDepositedOrbitalIssuedFilter (share)
open WilsonNeutralSignedPolynomialRate (read)
open FVA1Physical.TwoReset WilsonCoeffUV.Winding Further.PhysicalPeriodLimitF933 Macrame
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Embroider.Canvas FreeResolvent
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Pressure Precision Tree Exterior PertExtension PertExtension.Series WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open scoped Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner



open Source Labels
open WilsonOriginalFullRosterCouplingClock (work)
open WilsonReceivedChronologicalPanelClock (fare)
open WilsonOriginalOccupiedCorridor (sites)
open WilsonOriginalCensusAttendanceStation (Day)
open WilsonOriginalCensusPhysicalAttendance (roots tab Room)
open WilsonReceivedChronologicalPanelClock (debitDepth fare)
open WilsonOriginalOccupiedWindow WilsonOriginalOccupiedCorridor WilsonOriginalJointTrialHearing
open WilsonOriginalCensusPhysicalAttendance (Room roots tab)
open WilsonOriginalCensusFundedAttendance (Demand)
open WilsonReceivedChronologicalFixedLedger (Registered)
open WilsonReceivedChronologicalFixedEarner (programme)
open WilsonReceivedChronologicalFixedReserve (terms)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonOriginalCensusAttendanceStation
open AllOrder AllOrder.Floe
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonNeutralTwoPrintPathBoxHome (breadth)
open WilsonIndependentCollarOrbitalReception (relative)
open WilsonOriginalCensusCanonicalAngularMenu (repeated plottedLow)
open WilsonReceivedCanonicalSocketSeed (contact present)
open WilsonOriginalCensusDatedMaterial (Material words mounts)
open WilsonOriginalCensusFaceSites (binder port)
open WilsonOriginalCensusFaceSheet (Addressed)
open FundedMarkedPathSelection (output)
open WilsonReceivedFixedDigitCanonical (fixed)
open Comparison.Density.Transport
open WilsonOriginalCensusCanonicalFirstEdgePayer (Source)
open WilsonReceivedChronologicalFixedPlaced (Purchased)
open WilsonReceivedChronologicalFixedSocketLife
open WilsonReceivedChronologicalFixedCellFee
open WilsonReceivedChronologicalMaterialCapture (placed)
open WilsonReceivedChronologicalSocket (input)
open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonReceivedChronologicalFixedRoster
open WilsonReceivedChronologicalMaterialLine (homes)
open Function Set Filter MeasureTheory Analysis Table Spec Extraction Next.UVStress
open WilsonReceivedChronologicalMaterialSites
open StressFlux.Matching Cells WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking
open RG16 RG16.Literal
open Extra.Histories Extra.Trajectories Extra.Multi
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonMeasuredPublicEntranceCellWords (physical)
open WilsonMeasuredPublicEntrancePanel (Reading)
open Extra.Trajectories Extra.Multi
open WilsonOriginalTwoFlatIRCapturedCross (Quote)
open WilsonOriginalTwoFlatIRSocketPower (debt)
open WilsonReceivedChronologicalFixedRoseFittedDebit (written)
open WilsonReceivedChronologicalFixedRoseFigureTerms (Account)
open WilsonReceivedChronologicalFixedRoseTestSource (fixed)
universe h
variable {G:Gauge}(R:Run G)(simple:G.Simple){m j first N per:ℕ}{schedule:WilsonOriginalAllOrderCourse.Schedule G}
  {axis:Axis}{ε:ℝ}{T:Campaign R}{W:Campaign.Pillars R T}
  (funded:WilsonOriginalAllOrderCourse.Paid.{h} axis simple ε (WilsonOriginalOpticalSchedule.prepared schedule) R T W)
  (history:FundedOriginalVacuumPaths.prices R.kit)
  (role:Fin 3 → Fin 3)(lens:Fin 3 → ℕ)(pt:Fin 3 → Chamber)(caps:Fin 3 → ℝ)
  (covered:∀v,‖present lens v‖ ≤ caps v)
  (φ:Test 3)(requestedClass A:ℕ)(tol θ:ℝ)(tp:0<tol)(ep:0<θ)
  {U:Type}[Fintype U](teacher:ℕ)(tube:LinkTube G)(pieces groundPrice:ℕ)
  (pole:Bool → ℕ)(span:U → ℕ)(lag:U → Bool → ℕ)







variable (book:WilsonOriginalCensusPhysicalAttendance.Room ((WilsonOriginalOpticalSchedule.prepared schedule)) R simple)(training:ℝ)
  (resident:(M:ℕ) → m ≤ M → Day ((WilsonOriginalOpticalSchedule.prepared schedule)) R simple ((programme ((WilsonAddressedPublicSubmittedDates.grades role)) (((fun _:Fin 3=>(0:ℕ)))) ((WilsonAddressedPublicFirstRoseTerms.order R requestedClass + 1)))).school m M)
  {V:Realm G (((terms ((WilsonAddressedPublicSubmittedDates.grades role)) (((fun _:Fin 3=>(0:ℕ)))) ((WilsonAddressedPublicFirstRoseTerms.order R requestedClass + 1)))).order+1) Credit.leanC}(draw:V.draws=R.family.path.levels)
  (old:m ≤ first)(dates:first+1 ≤ j)(valid:j+1+1 ≤ N)
  (enrolled:WilsonReceivedChronologicalFixedRoseGridCampus.Slot funded role lens pt caps φ requestedClass A tol θ tp ep
    teacher tube pieces groundPrice pole span lag book training m resident V draw first j old dates per N valid)
  {f requested sourcePole names:ℕ}{B:ℝ}(fine:f ≤ j+1+1)(file:WilsonMovingForkHeterogeneousCut.Filed R ((WilsonAddressedPublicSubmittedDates.grades role)) (j+1+1))
  {r:ℝ}(rp:0<r)










private def face (s:Finset (Fin 3)):(Stock.census (Fin 3)).Mode:=⟨s,Finset.mem_univ _⟩

include enrolled covered rp in
theorem original (floorOld:WilsonSingleHardRadius.first R simple ≤ m)
    (activated:WilsonOriginalCensusCanonicalAppointedClock.opening R simple ((WilsonAddressedPublicFirstRoseCampus.seller G)) (((financed funded))) history (Burn.horizon ((programme ((WilsonAddressedPublicSubmittedDates.grades role)) (((fun _:Fin 3=>(0:ℕ)))) ((WilsonAddressedPublicFirstRoseTerms.order R requestedClass + 1)))).vac) ≤ m)
    {oldPrice:Credit}{Z:ℕ → SeriesA G}(quiet:WilsonOriginalCensusFiledAttendance.QuietAt ((resident N (old.trans ((Nat.le_succ first).trans (dates.trans ((Nat.le_succ j).trans ((Nat.le_succ (j+1)).trans valid))))))) oldPrice Z)
    (front:(t:Multi.Hot ((Stock.census (Fin 3)))) → t.val.val)
    {df:ℕ}{frame:Frame G df}(section_:SectionData frame)(group:Hol G)
    (forests:∀i:ℕ,∀u:Covers R.family.path.levels.S (i+1) (coarse R (i+1) per),Forest (step R (i+1) u.val).ratio)
    (chosen:∀i:ℕ,∀u:Covers R.family.path.levels.S (i+1) (coarse R (i+1) per),(step R (i+1) u.val).Choices)
    (upperFit₀:(WilsonAddressedPublicFirstRoseGeometry.Fits R.family.S (WilsonAddressedPublicFirstSites.original R draw φ).choose r first f))(lowerFit₀:(WilsonAddressedPublicFirstRoseGeometry.Fits R.family.S (WilsonReceivedChronologicalFixedCellFee.factor R φ) r first f))(before:first+1<(WilsonReceivedChronologicalFixedCellFee.capture R φ r))(sooner:(WilsonReceivedChronologicalFixedCellFee.capture R φ r)<f)(top:f<j+1+1)
    (big:2 ≤ R.alloy.B.a.clock.hatBeta ((WilsonReceivedChronologicalFixedCellFee.capture R φ r)))(licensed:(WilsonOriginalCensusPublicationClock.Open R simple ((WilsonAddressedPublicSubmittedDates.grades role)) ((programme ((WilsonAddressedPublicSubmittedDates.grades role)) (((fun _:Fin 3=>(0:ℕ)))) ((WilsonAddressedPublicFirstRoseTerms.order R requestedClass + 1)))).school.pieces (((programme ((WilsonAddressedPublicSubmittedDates.grades role)) (((fun _:Fin 3=>(0:ℕ)))) ((WilsonAddressedPublicFirstRoseTerms.order R requestedClass + 1)))).school.order+1) ((programme ((WilsonAddressedPublicSubmittedDates.grades role)) (((fun _:Fin 3=>(0:ℕ)))) ((WilsonAddressedPublicFirstRoseTerms.order R requestedClass + 1)))).load) ((WilsonReceivedChronologicalFixedCellFee.capture R φ r)))
    (clocked:(eventually_atTop.mp (WilsonOriginalTwoFlatIRRows.nextClock R simple)).choose ≤ (WilsonReceivedChronologicalFixedCellFee.capture R φ r))
    (ou:Trace.Physical.GermGraph.Opened R.family 0 m per)(ov:Trace.Physical.GermGraph.Opened R.family 0 (first+1) per)
    (ensemble:(WilsonReceivedChronologicalFixedRoseVariation.cells R φ r (f,per)) → WilsonMeasuredPublicEntrancePanel.Panel R ((WilsonAddressedPublicSubmittedDates.grades role)) N per f (j+1+1) fine valid requested sourcePole names B)
    (whereAt:∀y,(ensemble y).loc=y.val)(homesAt:∀y,(ensemble y).slot=file.station)(axesAt:∀y,(ensemble y).axis=file.A N per)
    (priorAt:∀_y:(WilsonReceivedChronologicalFixedRoseVariation.cells R φ r (f,per)),∀s:Finset (Fin 3),Selection R ((WilsonAddressedPublicSubmittedDates.grades role)) s → ∀i:ℕ,Config G (R.family.side i per) → Marker.Poly ((Stock.census (Fin 3))))
    (source:∀y,Reading R ((WilsonAddressedPublicSubmittedDates.grades role)) (ensemble y) ((old.trans (Nat.le_succ first)).trans (before.le.trans sooner.le)))
    (one:∀y i,1 ≤ (ensemble y).M i)(E:Fin 3 → ℕ)(refs:∀i k,k ≤ (WilsonAddressedPublicSubmittedDates.grades role) i → R.family.ref k ≤ N)
    (fare:∀y i,Next.Rank.Spindle.paid R.family ((WilsonAddressedPublicSubmittedDates.grades role) i) f N per ((ensemble y).names i) ≤ (ensemble y).M i*R.family.path.levels.clock.hatBeta f^(E i))
    (order:ℕ)(room:order+∑i,E i ≤ requested)
    {baseGoal p depth:ℕ}(promise:(WilsonAddressedPublicFirstRoseTerms.order R requestedClass)=baseGoal+2*sourcePole*3)
    (quote:Quote R N per m (first+1) ((WilsonReceivedChronologicalFixedCellFee.capture R φ r)) p depth ((old.trans (Nat.le_succ first)).trans before.le) before.le)
    (cp:1 ≤ (WilsonReceivedChronologicalFixedRoseEnrolledCash.roof training caps))(rent:0 ≤ ((Real.sqrt (R.family.path.β N per (first+1)))^(1:ℝ) * training^3))(cold:(Pert.Asymptotics.regulatorRun R.family N per) (first+1) ≤ 1)(coldK:(Pert.Asymptotics.regulatorRun R.family N per) (j+1+1) ≤ 1)
    (out:((Real.sqrt (R.family.path.β N per (first+1)))^(1:ℝ) * training^3) ≤ (WilsonReceivedChronologicalFixedRoseEnrolledCash.roof training caps)*(3*((Pert.Asymptotics.regulatorRun R.family N per) ((WilsonReceivedChronologicalFixedCellFee.capture R φ r)))⁻¹)^1)(cap:∀a,caps a ≤ (WilsonReceivedChronologicalFixedRoseEnrolledCash.roof training caps)*(3*((Pert.Asymptotics.regulatorRun R.family N per) ((WilsonReceivedChronologicalFixedCellFee.capture R φ r)))⁻¹)^1)
    (out₁:((Real.sqrt (R.family.path.β N per (first+1)))^(1:ℝ) * training^3) ≤ (WilsonReceivedChronologicalFixedRoseEnrolledCash.roof training caps)*(3*((Pert.Asymptotics.regulatorRun R.family N per) (first+1))⁻¹)^1)(cap₁:∀a,caps a ≤ (WilsonReceivedChronologicalFixedRoseEnrolledCash.roof training caps)*(3*((Pert.Asymptotics.regulatorRun R.family N per) (first+1))⁻¹)^1)
    (reach:∀s:Finset (Fin 3),4*(p+(WilsonOriginalTwoFlatIRHalo.power s.card ((∑a,(WilsonAddressedPublicSubmittedDates.grades role) a)+1+2+(2+2*3*1))+0+2)) ≤ depth)
    (Q goalEnd:ℕ)(kept:goalEnd+debt 3 1 (Fintype.card (Multi.Hot ((Stock.census (Fin 3))))) ≤ Q+1)(enough:Q ≤ ((terms ((WilsonAddressedPublicSubmittedDates.grades role)) (((fun _:Fin 3=>(0:ℕ)))) ((WilsonAddressedPublicFirstRoseTerms.order R requestedClass + 1)))).order):
    let plan:=WilsonReceivedChronologicalFixedRoseOriginalAccount.budget ((WilsonAddressedPublicSubmittedDates.grades role)) (((fun _:Fin 3=>(0:ℕ)))) ((WilsonAddressedPublicFirstRoseTerms.order R requestedClass + 1)) A sourcePole
      ((WilsonAddressedPublicFirstRoseTerms.order R requestedClass)) order p 1 goalEnd 1 B ((WilsonReceivedChronologicalFixedRoseEnrolledCash.roof training caps)) 100 θ θ ((WilsonReceivedChronologicalFixedRoseEnrolledCash.roof training caps))
    WilsonReceivedChronologicalFixedRoseGridFolio.Posted R ((WilsonAddressedPublicSubmittedDates.grades role)) lens pt φ r (c:=(WilsonReceivedChronologicalFixedCellFee.capture R φ r)) (v:=first+1)
      ((old.trans (Nat.le_succ first)).trans ((before.le.trans sooner.le).trans fine)) fine valid plan file ensemble draw first Q:=by
  classical
  intro plan
  unfold WilsonReceivedChronologicalFixedRoseGridFolio.Posted
  obtain ⟨classroom,_,teacherLow,atLow,sparse,period,current,geometry,rank,authorized,teacherHigh,go,board⟩:=enrolled
  let center:=WilsonReceivedChronologicalFixedCellFee.capture R φ r
  have equal:(R.family.path.rep N per center).p=R.family.path.levels.budget center:=
    (R.makes.wilson.represents N per center (sooner.le.trans (fine.trans valid))).vac
  have strip:(R.family.path.rep N per center).p.supportExponent ≤ 100:=by rw [equal,funded.support]
  have allRoom(s:Finset (Fin 3)):order+∑i∈s,E i ≤ requested:=
    (Nat.add_le_add_left (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun i _ _=>Nat.zero_le (E i))) order).trans room
  have back:j+1+1-2=j:=by omega
  have found:=WilsonReceivedChronologicalFixedRoseGridFiles.original
    (R:=R) (simple:=simple) (d:=(WilsonAddressedPublicSubmittedDates.grades role)) (P:=(WilsonAddressedPublicFirstRoseTerms.order R requestedClass + 1)) (school:=book) (day:=(resident N (old.trans ((Nat.le_succ first).trans (dates.trans ((Nat.le_succ j).trans ((Nat.le_succ (j+1)).trans valid))))))) (old:=old) (early:=(Nat.le_succ first).trans dates)
    (live:=valid) (lens:=lens) (pt:=pt) (toll:=((fun l:ℕ=>WilsonOriginalFixedTestCensusPublicBase.base training caps (((fun _:Fin 3=>(0:ℕ)))) (R.family.path.levels.clock.hatBeta (l+1))))) (classroom:=classroom) (fine:=fine) (file:=file)
    (paid:=covered) (role:=role) (roles:=rfl) (seller:=(WilsonAddressedPublicFirstRoseCampus.seller G)) (fund:=((financed funded))) (history:=history) (tube:=tube)
    ep tp (by simpa only [back] using authorized) activated rank rp upperFit₀.small upperFit₀.older upperFit₀.finer
    upperFit₀.margin ensemble whereAt homesAt axesAt priorAt lowerFit₀.small before sooner.le lowerFit₀.margin
    front (by simpa only [back] using teacherHigh) (atLow.trans (Nat.le_succ_of_le dates)) (by simpa only [back] using go)
    (by simpa only [back] using board) floorOld dates geometry funded.support section_ group promise quiet
    teacherLow atLow sparse period forests chosen current source one E refs fare order allRoom (by omega) big licensed clocked
    quote cp (by norm_num) rent out cap strip ou ov reach Q goalEnd cold coldK cp out₁ (fun a=>(covered a).trans (cap₁ a)) kept enough
  let data(y:(WilsonReceivedChronologicalFixedRoseVariation.cells R φ r (f,per)))(s:Finset (Fin 3)):=WilsonReceivedChronologicalFixedRoseGridFiles.entry
    (simple:=simple) (φ:=φ) (R:=R) (N:=N) (per:=per) (d:=(WilsonAddressedPublicSubmittedDates.grades role)) (P:=(WilsonAddressedPublicFirstRoseTerms.order R requestedClass + 1)) (school:=book) (day:=(resident N (old.trans ((Nat.le_succ first).trans (dates.trans ((Nat.le_succ j).trans ((Nat.le_succ (j+1)).trans valid)))))))
    (old:=old) (live:=valid) (lens:=lens) (pt:=pt) (toll:=((fun l:ℕ=>WilsonOriginalFixedTestCensusPublicBase.base training caps (((fun _:Fin 3=>(0:ℕ)))) (R.family.path.levels.clock.hatBeta (l+1))))) (classroom:=classroom) (fine:=fine)
    (panel:=ensemble y) (file:=file) (mask:=face s) (paid:=covered) (role:=role) (roles:=rfl) (prior:=priorAt y s)
    r before sooner.le order p 1 Q goalEnd 1 ((WilsonReceivedChronologicalFixedRoseEnrolledCash.roof training caps)) 100 ((WilsonReceivedChronologicalFixedRoseEnrolledCash.roof training caps))
  refine ⟨fun y s=>(data y s).basal,fun y s=>(data y s).firstStep,?_⟩
  intro y s
  have ident:(data y s).independent=WilsonReceivedChronologicalFixedRoseGridFolio.independent R ((WilsonAddressedPublicSubmittedDates.grades role)) lens pt φ r
    (c:=(WilsonReceivedChronologicalFixedCellFee.capture R φ r)) (v:=first+1) fine valid plan file ensemble draw first Q y s:=WilsonReceivedChronologicalFixedRoseGridField.original
    (R:=R) (simple:=simple) (d:=(WilsonAddressedPublicSubmittedDates.grades role)) (P:=(WilsonAddressedPublicFirstRoseTerms.order R requestedClass + 1)) (school:=book) (day:=(resident N (old.trans ((Nat.le_succ first).trans (dates.trans ((Nat.le_succ j).trans ((Nat.le_succ (j+1)).trans valid))))))) (old:=old) (live:=valid)
    (lens:=lens) (pt:=pt) (toll:=((fun l:ℕ=>WilsonOriginalFixedTestCensusPublicBase.base training caps (((fun _:Fin 3=>(0:ℕ)))) (R.family.path.levels.clock.hatBeta (l+1))))) (classroom:=classroom) (fine:=fine) (panel:=ensemble y) (file:=file)
    (mask:=face s) (paid:=covered) (role:=role) (roles:=rfl) (prior:=priorAt y s) r before sooner.le order p 1 Q goalEnd 1
    ((WilsonReceivedChronologicalFixedRoseEnrolledCash.roof training caps)) 100 ((WilsonReceivedChronologicalFixedRoseEnrolledCash.roof training caps)) y.val (whereAt y)
  rw [←ident]
  exact (found y s).2

end YM.Integration.WilsonReceivedChronologicalFixedRoseGridPurchase
end
