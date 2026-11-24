import YM.Integration.WilsonReceivedChronologicalRosterCapturedArchive
import YM.Integration.WilsonReceivedChronologicalFixedRoseGridDeposit
import YM.Integration.WilsonReceivedChronologicalFixedRoseGridOrigin
import YM.Integration.WilsonOriginalTwoFlatIRPoolSubfaceCourse
import YM.Integration.WilsonOriginalTwoFlatIRPoolSubfaceMaterial

/-! Archive one original emitted sheet per full socket. Each ordinary face retains its own coefficients. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterCapturedFields
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary QuadraticLocal.Affinity
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision Tree Exterior PhysicalNext.Repeat.Legato
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada FVA1Physical.TwoReset
open WilsonVacuumPreResetStationaryChange WilsonOriginalPrimerReplicatedInk PhysicalForestMarkedRay PhysicalForestRay
open FreeResolvent WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonOriginalPointCompactRoster WilsonOriginalThreeCopiedCharts
open scoped Classical BigOperators ContDiff Topology
open LocalComparison Comparison.RG02.Cumulants Comparison.RG02.Assembly Order AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalThreePurchasedRays (prescribed)
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet WilsonOriginalCensusCopySlate
open WilsonOlderFreshGraphSlate (Copy)
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical
open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology
open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedPin WilsonOlderFreshConnectedAppointment FundedMarkedCoverRows
open WilsonCoeffUV.Bank.Ticket
open WilsonNeutralTwoPrintPathCensus (slates)
open WilsonNeutralTwoPrintPathJet (diagonal)
open WilsonOriginalCensusDatedMaterial (Material charts)
open WilsonReceivedDepositedOrbitalPages (offered)
open WilsonReceivedDepositedOrbitalPrint (front)
open WilsonReceivedCompactVerseEntrance
open WilsonReceivedCoverGrade (Same)
open WilsonOriginalCensusFaceSites (binder pin)
open WilsonReceivedDepositedSocketRows (entered)
open WilsonOriginalCensusDatedMaterial (charts)
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedFixedDigitCanonical (fixed)
open OriginalMarkedSourceComet
open WilsonOriginalCensusDatedSheets (sideValue)
open WilsonOriginalCensusFaceSheet (Addressed)
open WilsonOriginalRawQReversion (coordinates)
open AllOrder AllOrder.Floe QuadraticLocal QuadraticLocal.Rebirth
open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonThermometerDeclaredSeeds
open WilsonCoeffUV.Bank.Carp
open WilsonNeutralTwoPrintPathItinerary
open WilsonReceivedDepositedOrbitalNamedWage (wages)
open WilsonReceivedDepositedOrbitalNameWages (central)
open WilsonReceivedDepositedOrbitalFixedMoments (program)
open WilsonOriginalCensusFiniteLedger (reading)
open WilsonOriginalCensusDatedMaterial (words mounts)
open WilsonOriginalCensusFaceSites (port)
open WilsonOriginalCensusDeckMean (mean)
open WilsonCoeffUV.Wheel.Address WilsonIndependentCollarOrbitShapes
open WilsonNeutralTwoPrintPathBoxHome (radius)
open PertExtension.Series AllOrder.Floe
open WilsonOriginalCensusAngularFace (sides)
open WilsonOriginalSparseFiledOpening (near)
open WilsonOriginalCensusFaceSites (binder port pin)
open WilsonOriginalCensusDatedMaterial (Material words mounts)
open FVA1Physical.TwoReset QuadraticLocal.Earn QuadraticLocal.Mentor
open QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary
open WilsonOriginalCensusPhysicalLoad
open WilsonOriginalCensusPhysicalAttendance (Room)
open WilsonOriginalCensusFundedAttendance (Demand)
open WilsonOriginalCensusAttendanceStation (Day)
open WilsonReceivedChronologicalPanelClock (fare)
open WilsonOriginalOccupiedCorridor (sites)
open WilsonOriginalCensusFiledAttendance (QuietAt)
open WilsonOriginalOpticalSchedule (prepared)
open WilsonOriginalCensusFundedAttendance (quote)
open WilsonReceivedChronologicalFixedEarner (programme start)
open WilsonReceivedChronologicalFixedLedger (Registered)
open WilsonReceivedChronologicalMaterialLine (homes)
open WilsonReceivedChronologicalMaterialRoster (Filed)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonOriginalFullRosterCouplingClock (work)
open WilsonReceivedChronologicalDualInterval (Owned)
open WilsonReceivedChronologicalFixedReserve (terms charges)
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor QuadraticLocal.Affinity
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport Pert.Asymptotics
open WilsonOriginalCensusAngularFace
open WilsonReceivedChronologicalMaterialApertures (spread diameter)
open WilsonReceivedChronologicalFixedTariff (gross)
open WilsonReceivedChronologicalFixedMonth (Sheets)
open WilsonReceivedChronologicalLastFlat (Ticket wage)
open WilsonOriginalJointTrialHearing (fee)
open Function Set Filter MeasureTheory Analysis Table Spec Extraction Next.UVStress
open StressFlux.Matching Cells WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking
open WilsonReceivedChronologicalMaterialCapture (placed)
open WilsonReceivedChronologicalFixedEnrollment (Cohort)
open WilsonReceivedChronologicalFixedProgram (printed)
open WilsonReceivedChronologicalFixedPorts (Period)
open WilsonReceivedChronologicalFixedCohortFee (Earned)
open WilsonReceivedChronologicalFixedCellFee (factor positive capture tape)
open WilsonReceivedChronologicalFixedPlaced (Purchased)
open WilsonReceivedChronologicalSocket (extend lit input)
open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonReceivedCanonicalVersePosterior (word)
open WilsonMovingForkPrintedFile (parent)
open WilsonMovingForkStencilLine (Received)
open WilsonMovingForkDepositedPrint (Sheet)
open WilsonMovingForkPrintedFile (allSlots parent)
open WilsonMovingForkStencilCatalogue (Catalogue)
open WilsonMovingForkStencilProgramme (Basis)
open WilsonMovingForkStencilLine (Received)
open WilsonMovingForkDepositedPrint (Sheet)
open WilsonOriginalTwoFlatIRPoolSubfaceCourse (expanded)
open WilsonReceivedChronologicalRosterCatalogue (Ages)
open WilsonAddressedPublicFirstRoseGeometry (Fits)

variable {G : Gauge} {n m first j f : ℕ} {R : Run G} {simple : G.Simple}
  {schedule : WilsonOriginalAllOrderCourse.Schedule G} {grades : Fin n → ℕ}
  (power : Fin n → ℕ) (P : ℕ) (house : Room (prepared schedule) R simple)
  (resident : (N : ℕ) → m ≤ N → Day (prepared schedule) R simple (programme grades power P).school m N)
  {V : Realm G ((terms grades power P).order+1) Credit.leanC} {draw : V.draws = R.family.path.levels}
  (rate : ℕ → ℕ → ℝ) (allowance : ℝ) {dims : Fin n → ℕ} (test : Case dims)
  (κ : (v : Fin n) → Knob (dims v)) (pt : Fin n → Chamber)
  (toll : ℕ → Fin n → ℝ) (old : m ≤ first) (early : first+1 ≤ j)
  (φ : Test n) (caps : Fin n → ℝ) (A target : ℕ) (η : ℝ)
  (paid : ∀v, ‖test v‖ ≤ caps v) (fine : f ≤ j+1+1) 

private theorem residentAt {m first j N : ℕ} (old : m ≤ first) (early : first+1 ≤ j)
    (valid : j+1+1 ≤ N) : m ≤ N := by omega

local notation "K" => j+1+1
local notation "issuedDay" N:max valid:max => resident N (residentAt old early valid)
private theorem birthAt {first j:ℕ} (early:first+1 ≤ j) : first+1 ≤ j+1+1 :=
  early.trans ((Nat.le_succ j).trans (Nat.le_succ (j+1)))
local notation "supports" => WilsonReceivedChronologicalRosterCapturedArchive.Occupied (n:=n) R fine (birthAt early)
local notation "active" => (show first+1 ≤ K by omega)
local notation "camp" N:max per:max valid:max => Purchased (per:=per) (V:=V) (draw:=draw)
  (rate:=rate N per) (allowance:=allowance) power P house (issuedDay N valid) κ pt K first valid toll old φ caps A target η
local notation "admission" => fun N per (valid : K ≤ N) => camp N per valid

private def source {N per : ℕ} {valid : K ≤ N} (pupil : camp N per valid)
    (y : supports per) (q : Basis R grades) (a : Ages first K) :
    Sheet R N (a.val+1) (parent R (by have h := mem_Ico.mp a.property; omega : a.val+1 ≤ K)
      per (placed R fine y.val)) :=
  WilsonReceivedChronologicalFixedRoseGridDeposit.deposit (j:=j) (R:=R) (per:=per) (V:=V) (draw:=draw)
    (rate:=rate N per) (allowance:=allowance) (power:=power) (P:=P) (house:=house) (day:=issuedDay N valid)
    (κ:=κ) (pt:=pt) (top:=K) (first:=first) (valid:=valid) (toll:=toll) (old:=old) (test:=test)
    (classroom:=pupil) (fine:=fine) (z:=(y).val) (s:=allSlots n) (q:=q) (paid:=paid)
    active y.property a

local notation "paper" => source (V:=V) (draw:=draw) power P house resident rate allowance test κ pt toll old early
  φ caps A target η paid fine

local notation "liveRow" pupil:max y:max s:max q:max hd:max prior:max σ:max =>
  WilsonReceivedChronologicalFixedSocketLife.line (R:=R) (V:=V) (draw:=draw) (power:=power) (P:=P)
    (house:=house) (κ:=κ) (pt:=pt) (top:=K) (first:=first) (toll:=toll) (old:=old) (test:=test)
    (classroom:=pupil) (fine:=fine) (z:=(y).val) (s:=s) (q:=q) (paid:=paid) (hd:=hd) (prior:=prior) (σ:=σ)

/-- The catalogue covers every funded captured placement before the field, the thermal parameter and both regulators. The stored
sheet is the original dated physical emission, also for every exposed subface and its vacuum. -/
theorem original :
    ∃ book : Catalogue R grades K, ∀ (N per : ℕ) (valid : K ≤ N) (pupil : camp N per valid),
      ∀ (y : supports per) (s : (Stock.census (Fin n)).Mode) (q : Selection R grades s.val)
        (a : Ages first K), let H := paper pupil y (expanded R grades s q) a
        book N per (placed R fine y.val) (expanded R grades s q) (a.val+1)
            (by have h := mem_Ico.mp a.property; omega) = some H ∧
          ∀ (hd : ∀v, 0 < grades v)
            (prior : (i : ℕ) → Config G (R.family.side i per) → Marker.Poly (Stock.census (Fin n))) (σ : ℝ),
            WilsonMovingForkStencilLine.Received H ((liveRow pupil y s q hd prior σ) (a.val+1)) := by
  classical
  obtain ⟨book, filed⟩ := WilsonReceivedChronologicalRosterCapturedArchive.stored R grades fine active
    (admission) (fun {_ _ _} pupil y q a => paper pupil y q a)
  refine ⟨book, ?_⟩
  intro N per valid pupil y s q a H
  refine ⟨filed N per valid pupil y (expanded R grades s q) a, ?_⟩
  intro hd prior σ
  have aligned := WilsonOriginalTwoFlatIRPoolSubfaceCourse.original (R:=R) (per:=per) (V:=V) (draw:=draw)
    (power:=power) (P:=P) (house:=house) (day:=issuedDay N valid) (κ:=κ) (pt:=pt)
    (top:=K) (first:=first) (valid:=valid) (toll:=toll) (old:=old) (test:=test)
    (classroom:=pupil) (fine:=fine) (z:=(y).val) (s:=s) (q:=q) (paid:=paid) (hd:=hd) (prior:=prior) (σ:=σ)
  rw [aligned]
  exact WilsonReceivedChronologicalFixedRoseGridDeposit.received (j:=j) (R:=R) (per:=per) (V:=V) (draw:=draw)
    (rate:=rate N per) (allowance:=allowance) (power:=power) (P:=P) (house:=house) (day:=issuedDay N valid)
    (κ:=κ) (pt:=pt) (top:=K) (first:=first) (valid:=valid) (toll:=toll) (old:=old) (test:=test)
    (classroom:=pupil) (fine:=fine) (z:=(y).val) (s:=allSlots n) (q:=expanded R grades s q) (paid:=paid)
    (hd:=hd) (prior:=prior) (σ:=σ) active y.property a

end YM.Integration.WilsonReceivedChronologicalRosterCapturedFields
end
