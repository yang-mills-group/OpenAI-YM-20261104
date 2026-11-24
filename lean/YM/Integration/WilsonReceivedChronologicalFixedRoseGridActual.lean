import YM.Integration.WilsonReceivedChronologicalFixedRoseGridPayroll
import YM.Integration.WilsonReceivedChronologicalFixedRoseGridPurchase
import YM.Integration.WilsonReceivedChronologicalFixedRoseGridGates
import YM.Integration.WilsonReceivedChronologicalFixedRoseGridStock
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
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseGridActual
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
open WilsonReceivedChronologicalFixedRoseGridStock
open WilsonReceivedChronologicalFixedRoseGridFolio (Posted)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntrancePanel (Panel Reading)
open WilsonReceivedChronologicalFixedRoseVariation (cells)
variable {G:Gauge}(R:Run G)(simple:G.Simple){m j first f K:ℕ}{schedule:WilsonOriginalAllOrderCourse.Schedule G}
  {axis:Axis}{ε:ℝ}{T:Campaign R}{W:Campaign.Pillars R T}
  (funded:WilsonOriginalAllOrderCourse.Paid.{h} axis simple ε (WilsonOriginalOpticalSchedule.prepared schedule) R T W)
  (history:FundedOriginalVacuumPaths.prices R.kit)
  (role:Fin 3 → Fin 3)(lens:Fin 3 → ℕ)(pt:Fin 3 → Chamber)(caps:Fin 3 → ℝ)
  (covered:∀i,‖present lens i‖ ≤ caps i)
  (φ:Test 3)(requestedClass A:ℕ)(tol η:ℝ)(tp:0 < tol)(ep:0 < η)
  {I:Type}[Fintype I](teacher:ℕ)(tube:LinkTube G)(pieces assignment:ℕ)
  (orders:Bool → ℕ)(span:I → ℕ)(lag:I → Bool → ℕ)






variable (book:WilsonOriginalCensusPhysicalAttendance.Room ((WilsonOriginalOpticalSchedule.prepared schedule)) R simple)(training:ℝ)
  (resident:(N:ℕ) → m ≤ N → Day ((WilsonOriginalOpticalSchedule.prepared schedule)) R simple ((programme ((WilsonAddressedPublicSubmittedDates.grades role)) (((fun _:Fin 3=>(0:ℕ)))) (((WilsonAddressedPublicFirstRoseTerms.order R requestedClass))+1))).school m N)
  {X:Realm G (((terms ((WilsonAddressedPublicSubmittedDates.grades role)) (((fun _:Fin 3=>(0:ℕ)))) (((WilsonAddressedPublicFirstRoseTerms.order R requestedClass))+1))).order+1) Credit.leanC}(draw:X.draws=R.family.path.levels)
  (old:m ≤ first)(dated:first+1 ≤ j)(ks:j+1+1=K){r:ℝ}(rp:0 < r)



variable (before:first+1 < (WilsonReceivedChronologicalFixedCellFee.capture R φ r))(inside:(WilsonReceivedChronologicalFixedCellFee.capture R φ r) < f)(fk:f < K)





variable {pole requested tag:ℕ}{B:ℝ}(file:Filed R ((WilsonAddressedPublicSubmittedDates.grades role)) (K))
open WilsonReceivedChronologicalFixedRoseOriginalAccount (budget)
open WilsonOriginalTwoFlatIRSocketPower (debt)




include covered rp in
theorem original (order:Extraction.Order)(l:Filter (ℕ×ℕ))(belongs:l ≤ order.fuse)
    (floorOld:WilsonSingleHardRadius.first R simple ≤ m)
    (activated:WilsonOriginalCensusCanonicalAppointedClock.opening R simple (WilsonAddressedPublicFirstRoseCampus.seller G)
      (financed funded) history (Burn.horizon ((programme ((WilsonAddressedPublicSubmittedDates.grades role)) (((fun _:Fin 3=>(0:ℕ)))) (((WilsonAddressedPublicFirstRoseTerms.order R requestedClass))+1))).vac) ≤ m)
    {oldPrice:Credit}(quiet:∀N,∀live:m ≤ N,∃Z:ℕ → SeriesA G,WilsonOriginalCensusFiledAttendance.QuietAt (resident N live) oldPrice Z)
    (freshGate:((WilsonReceivedChronologicalFixedRoseGridGates.original R simple ((WilsonAddressedPublicSubmittedDates.grades role)) (((WilsonAddressedPublicFirstRoseTerms.order R requestedClass))+1))).choose ≤ m)(refGate:frontage R ((WilsonAddressedPublicSubmittedDates.grades role)) ≤ m)
    (upperRooms:(WilsonAddressedPublicFirstRoseGeometry.Fits R.family.S (WilsonAddressedPublicFirstSites.original R draw φ).choose r first f))(lowerRooms:(WilsonAddressedPublicFirstRoseGeometry.Fits R.family.S (WilsonReceivedChronologicalFixedCellFee.factor R φ) r first f))
    (E:Fin 3 → ℕ)(arrival:ℕ)(salary:arrival+∑i,E i ≤ requested)
    (baseGoal p infrared Q goalEnd:ℕ)(promise:(WilsonAddressedPublicFirstRoseTerms.order R requestedClass)=baseGoal+2*pole*3)
    (cross:crossed ((WilsonAddressedPublicSubmittedDates.grades role)) p ≤ infrared)
    (kept:goalEnd+debt 3 1 (Fintype.card (Multi.Hot (Stock.census (Fin 3)))) ≤ Q+1)
    (enough:Q ≤ ((terms ((WilsonAddressedPublicSubmittedDates.grades role)) (((fun _:Fin 3=>(0:ℕ)))) (((WilsonAddressedPublicFirstRoseTerms.order R requestedClass))+1))).order)
    (writtenAt:∀ᶠper:ℕ in atTop,∀N:ℕ,∀kn:(K) ≤ N,
      let rate:=(Real.sqrt (R.family.path.β N per (first+1)))^(1:ℝ)*training^3
      let money:=max (max 1 (training^3)) (∑i,|caps i|)
      let g:=Pert.Asymptotics.regulatorRun R.family N per
      WilsonOriginalTwoFlatIRCapturedCross.Quote R N per m (first+1) ((WilsonReceivedChronologicalFixedCellFee.capture R φ r)) p infrared ((((old.trans (Nat.le_succ first)).trans before.le))) before.le ∧
      1 ≤ money ∧ 0 ≤ rate ∧ 0 < g (first+1) ∧ g (first+1) ≤ 1 ∧ g (K) ≤ 1 ∧
      rate ≤ money*(3*(g ((WilsonReceivedChronologicalFixedCellFee.capture R φ r)))⁻¹)^1 ∧ (∀i,caps i ≤ money*(3*(g ((WilsonReceivedChronologicalFixedCellFee.capture R φ r)))⁻¹)^1) ∧
      rate ≤ money*(3*(g (first+1))⁻¹)^1 ∧ (∀i,caps i ≤ money*(3*(g (first+1))⁻¹)^1) ∧ (WilsonReceivedChronologicalFixedRoseGridCampus.Slot funded role lens pt caps φ requestedClass A tol η tp ep teacher tube pieces assignment orders span lag book training m resident X draw first j old dated) per N (ks.le.trans kn))
    (stamp:∀N per:ℕ,∀kn:(K) ≤ N,
      (cells R φ r (f,per) → Panel R ((WilsonAddressedPublicSubmittedDates.grades role)) N per f (K) fk.le kn requested pole tag B) → Prop)
    (originalSource:∀N per:ℕ,∀kn:(K) ≤ N,
      ∃Y:cells R φ r (f,per) → Panel R ((WilsonAddressedPublicSubmittedDates.grades role)) N per f (K) fk.le kn requested pole tag B,
      stamp N per kn Y ∧ ∀y,Reading R ((WilsonAddressedPublicSubmittedDates.grades role)) (Y y) ((((old.trans (Nat.le_succ first)).trans (before.le.trans inside.le)))) ∧ (Y y).loc=y.val ∧
      (Y y).slot=file.station ∧ (Y y).axis=file.A N per ∧ (∀i,1 ≤ (Y y).M i) ∧
      (∀i,Next.Rank.Spindle.paid R.family ((WilsonAddressedPublicSubmittedDates.grades role) i) f N per ((Y y).names i) ≤ (Y y).M i*R.family.path.levels.clock.hatBeta f^(E i)))
    (prior:∀per:ℕ,∀_:cells R φ r (f,per),∀s:Finset (Fin 3),Selection R ((WilsonAddressedPublicSubmittedDates.grades role)) s → 
      ∀i:ℕ,Config G (R.family.side i per) → Marker.Poly (Stock.census (Fin 3))):
    let plan:=budget ((WilsonAddressedPublicSubmittedDates.grades role)) (((fun _:Fin 3=>(0:ℕ)))) (((WilsonAddressedPublicFirstRoseTerms.order R requestedClass))+1) A pole ((WilsonAddressedPublicFirstRoseTerms.order R requestedClass)) arrival p 1 goalEnd 1 B ((WilsonReceivedChronologicalFixedRoseEnrolledCash.roof training caps)) 100 η η ((WilsonReceivedChronologicalFixedRoseEnrolledCash.roof training caps))
    ∀ᶠpair in l,∃kn:(K) ≤ pair.1,
      ∃Y:cells R φ r (f,pair.2) → Panel R ((WilsonAddressedPublicSubmittedDates.grades role)) pair.1 pair.2 f (K) fk.le kn requested pole tag B,
      stamp pair.1 pair.2 kn Y ∧
        Posted R ((WilsonAddressedPublicSubmittedDates.grades role)) lens pt φ r (c:=(WilsonReceivedChronologicalFixedCellFee.capture R φ r)) (v:=first+1) (((((((old.trans (Nat.le_succ first)).trans (before.le.trans inside.le)))).trans fk.le))) fk.le kn plan file Y draw first Q:=by
  subst K
  exact WilsonReceivedChronologicalFixedRoseGridPayroll.original
    (R:=R) (simple:=simple) (funded:=funded) (history:=history) (role:=role) (lens:=lens) (pt:=pt)
    (caps:=caps) (covered:=covered) (φ:=φ) (requestedClass:=requestedClass) (A:=A)
    (tol:=tol) (η:=η) (tp:=tp) (ep:=ep) (teacher:=teacher) (tube:=tube) (pieces:=pieces) (assignment:=assignment)
    (orders:=orders) (span:=span) (lag:=lag) (book:=book) (training:=training) (resident:=resident)
    (draw:=draw) (old:=old) (dated:=dated) (rp:=rp) (before:=before) (inside:=inside) (fk:=fk) (file:=file)
    order l belongs floorOld activated quiet freshGate refGate upperRooms lowerRooms E arrival salary
    baseGoal p infrared Q goalEnd promise cross kept enough writtenAt stamp originalSource prior
end YM.Integration.WilsonReceivedChronologicalFixedRoseGridActual
end
