import YM.Integration.WilsonReceivedChronologicalFixedRoseGridCatalogue
import YM.Integration.WilsonReceivedChronologicalFixedRoseGridArchive

/-! Before either cutoff, archive the appointed physical material on the complete supported grid. -/
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseGridWitness
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
  (old:m ≤ first)(dates:first+1 ≤ j)
variable {f:ℕ}(fine:f≤j+1+1)(r:ℝ)(rp:0<r)
  (hi:WilsonAddressedPublicFirstRoseGeometry.Fits R.family.S (WilsonAddressedPublicFirstSites.original R draw φ).choose r first f)
  (lo:WilsonAddressedPublicFirstRoseGeometry.Fits R.family.S (factor R φ) r first f)
open WilsonMovingForkPrintedFile (parent)
open WilsonMovingForkStencilProgramme (Basis)
open WilsonMovingForkStencilCatalogue (Catalogue)
open WilsonMovingForkStencilLine (Received)
open WilsonReceivedChronologicalFixedRoseGridArchive (Ledger catalogue)
open WilsonReceivedChronologicalFixedRoseVariation (cells)
local notation "k₀" => WilsonAddressedPublicSubmittedDates.grades role

/-- The original fiscal record on the supported finite cells, with its appointed upper date and residents. -/
def Occupied {K:ℕ} (fk:f≤K) (deposited:Catalogue R (k₀) K) : Prop :=
  ∃(room₀:WilsonOriginalCensusPhysicalAttendance.Room (WilsonOriginalOpticalSchedule.prepared schedule) R simple)
    (inhabitants:(N:ℕ) → m≤N → Day (WilsonOriginalOpticalSchedule.prepared schedule) R simple
      (programme (k₀) (fun _:Fin 3=>0) (WilsonAddressedPublicFirstRoseTerms.order R requestedClass+1)).school m N)
    (j:ℕ),j=K-2 ∧ ∃(dates:first+1≤j)(ks:j+1+1=K)(pos:0<r)
      (upper:WilsonAddressedPublicFirstRoseGeometry.Fits R.family.S (WilsonAddressedPublicFirstSites.original R draw φ).choose r first f)
      (lower:WilsonAddressedPublicFirstRoseGeometry.Fits R.family.S (factor R φ) r first f),
    ∀ᶠper:ℕ in atTop,∀(N:ℕ)(valid:K≤N),
      ∃entered:WilsonReceivedChronologicalFixedRoseGridCampus.Slot funded role lens pt caps φ requestedClass A tol θ tp ep
        teacher tube pieces groundPrice pole span lag room₀ training m inhabitants V draw first j old dates per N (ks.le.trans valid),
      WilsonReceivedChronologicalFixedRoseGridCatalogue.Enrolled (R:=R) (simple:=simple) (funded:=funded) (role:=role) (lens:=lens) (pt:=pt)
    (covered:=covered) (φ:=φ) (caps:=caps) (requestedClass:=requestedClass) (A:=A)
    (tol:=tol) (θ:=θ) (tp:=tp) (ep:=ep) (teacher:=teacher) (tube:=tube) (pieces:=pieces)
    (groundPrice:=groundPrice) (pole:=pole) (span:=span) (lag:=lag) (book:=room₀) (training:=training) (resident:=inhabitants)
    (V:=V) (draw:=draw) (old:=old) (dates:=dates) (fine:=fk.trans ks.ge) (r:=r)
    (rp:=pos) (hi:=upper) (lo:=lower) (ks.symm ▸ deposited) per N (ks.le.trans valid) entered

include rp hi lo in
omit [Fintype U] in
theorem original {K:ℕ} (fk:f≤K) (ks:j+1+1=K) (current:j=K-2)
    (openings:∀ᶠper:ℕ in atTop,∀(N:ℕ)(valid:K≤N),WilsonReceivedChronologicalFixedRoseGridCampus.Slot funded role lens pt caps φ requestedClass A tol θ tp ep
        teacher tube pieces groundPrice pole span lag
        book training m resident V draw first j old dates per N (ks.le.trans valid)):
    ∃deposited:Catalogue R (k₀) K,Occupied (R:=R) (simple:=simple) (funded:=funded) (role:=role) (lens:=lens) (pt:=pt)
    (covered:=covered) (φ:=φ) (caps:=caps) (requestedClass:=requestedClass) (A:=A)
    (tol:=tol) (θ:=θ) (tp:=tp) (ep:=ep) (teacher:=teacher) (tube:=tube) (pieces:=pieces)
    (groundPrice:=groundPrice) (pole:=pole) (span:=span) (lag:=lag) (training:=training)
    (V:=V) (draw:=draw) (old:=old) (r:=r) fk deposited:=by
  subst K
  obtain ⟨deposited,booked⟩:=WilsonReceivedChronologicalFixedRoseGridCatalogue.original (R:=R) (simple:=simple) (funded:=funded) (role:=role) (lens:=lens) (pt:=pt)
    (covered:=covered) (φ:=φ) (caps:=caps) (requestedClass:=requestedClass) (A:=A)
    (tol:=tol) (θ:=θ) (tp:=tp) (ep:=ep) (teacher:=teacher) (tube:=tube) (pieces:=pieces)
    (groundPrice:=groundPrice) (pole:=pole) (span:=span) (lag:=lag) (book:=book) (training:=training) (resident:=resident)
    (V:=V) (draw:=draw) (old:=old) (dates:=dates) (fine:=fk) (r:=r)
    (rp:=rp) (hi:=hi) (lo:=lo) openings
  exact ⟨deposited,book,resident,j,current,dates,rfl,rp,hi,lo,booked⟩

end YM.Integration.WilsonReceivedChronologicalFixedRoseGridWitness
end
