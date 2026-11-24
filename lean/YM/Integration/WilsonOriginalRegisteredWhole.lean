import YM.Integration.WilsonOriginalMaterialWhole
import YM.Integration.WilsonReceivedChronologicalFixedLedger
import YM.Integration.WilsonReceivedChronologicalFixedEarner
import YM.Integration.WilsonReceivedChronologicalMaterialStream
import YM.Integration.WilsonReceivedChronologicalFixedRoster
/-! Each member of the selected finite interval retains its original occupied source on the fixed older day. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalRegisteredWhole
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
open WilsonOriginalCensusFaceSheet (Addressed)
open WilsonOriginalCensusFaceSites (binder port pin)
open WilsonOriginalCensusDatedMaterial (Material words mounts)
open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonReceivedDepositedOrbitalNamedWage (wages)
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

open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor QuadraticLocal.Affinity
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport Pert.Asymptotics
open WilsonOriginalCensusAngularFace
open scoped BigOperators Classical


open WilsonReceivedChronologicalFixedReserve (terms)
open WilsonReceivedChronologicalFixedEarner (programme)
open WilsonReceivedChronologicalMaterialRoster (Filed)
open WilsonReceivedChronologicalMaterialLine (homes)
open WilsonReceivedChronologicalMaterialEndpoint (submitted)
open WilsonReceivedChronologicalMaterialStream (stream entered)
open WilsonIndependentCollarDatedPrior (onLevels)
variable {G:Gauge}{n o m N K per:ℕ}{grades:Fin n  →  ℕ}{R:Run G}{simple:G.Simple}
  {schedule:WilsonOriginalAllOrderCourse.Schedule G}(power:Fin n  →  ℕ)(P:ℕ)
  (house:Room (prepared schedule) R simple)(day:Day (prepared schedule) R simple (programme grades power P).school o N)
  {dims:Fin n → ℕ}{V:Realm G ((terms grades power P).order+1) Credit.leanC}{draw:V.draws=R.family.path.levels}
  {rate allowance:ℝ}(digits:Digits V.draws (Fin n))(test:Case dims)(κ:(v:Fin n)  →  Knob (dims v))
  (pt:Fin n  →  Chamber)(seed:(v:Fin n)  →  Choice R grades v)(wallet:Wallet (room (Fin n)))

local notation "roots₀" => WilsonOriginalCensusPhysicalAttendance.roots (prepared schedule) R simple
local notation "tab₀" => WilsonOriginalCensusPhysicalAttendance.tab (prepared schedule) R simple
local notation "clock₀" => R.alloy.B.a.clock
local notation "ask₀" => programme grades power P
local notation "q₀" => (terms grades power P).order
local notation "grid" a:max => R.family.side ((a)+1) per

open WilsonReceivedChronologicalFixedLedger (Registered)
open MeasureTheory

theorem original (age:ℕ)(ready:o≤age)(live:age<N)(z:Fin n → Cover)(w:Fin n→ℝ)
    (raw:Config G (grid age)→Marker.Poly (Stock.census (Fin n)))
    (entry:Registered (K:=K) (per:=per) (draw:=draw) (rate:=rate) (allowance:=allowance) power P house day
      digits test κ pt seed wallet age ready live z w raw):Integrable raw (prior G _):=by
  obtain ⟨op,_seats,_class,sold⟩:=entry.paid
  rw [entry.source]
  exact WilsonOriginalMaterialWhole.original (paid:=sold 1 zero_lt_one) (x:=wallet) ..

end YM.Integration.WilsonOriginalRegisteredWhole
end
