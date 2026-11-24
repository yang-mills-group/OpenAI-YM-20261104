import YM.Integration.WilsonOriginalRegisteredWhole
import YM.Integration.WilsonMovingForkPostedMaterial

/-! The full deposited response at the actual finite original receiver of a registered row. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.WilsonMovingForkRegisteredMaterial
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
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet WilsonOriginalCensusCopySlate
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
open WilsonReceivedCompactVerseEntrance
open WilsonOriginalCensusFaceSites (binder pin)
open WilsonReceivedFixedDigitHistory (Digits)
open OriginalMarkedSourceComet
open AllOrder AllOrder.Floe QuadraticLocal QuadraticLocal.Rebirth
open WilsonThermometerDeclaredSeeds
open WilsonCoeffUV.Bank.Carp
open WilsonNeutralTwoPrintPathItinerary
open WilsonOriginalCensusFaceSites (port)
open WilsonCoeffUV.Wheel.Address WilsonIndependentCollarOrbitShapes
open PertExtension.Series AllOrder.Floe
open WilsonOriginalCensusFaceSites (binder port pin)
open FVA1Physical.TwoReset QuadraticLocal.Earn QuadraticLocal.Mentor
open QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary
open WilsonOriginalCensusPhysicalLoad
open WilsonOriginalCensusPhysicalAttendance (Room)
open WilsonOriginalCensusAttendanceStation (Day)
open WilsonOriginalOpticalSchedule (prepared)
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
open WilsonReceivedChronologicalFixedLedger (Registered)
open WilsonMovingForkDepositedPrint (board polynomial)
open WilsonOriginalCensusFaceSites (port)
open WilsonOriginalTwoFlatIRMounted (value)
open MeasureTheory

variable {G:Gauge}{n o N K per:ℕ}{grades:Fin n  →  ℕ}{R:Run G}{simple:G.Simple}
  {schedule:WilsonOriginalAllOrderCourse.Schedule G}(power:Fin n  →  ℕ)(P:ℕ)
  (house:Room (prepared schedule) R simple)(day:Day (prepared schedule) R simple (programme grades power P).school o N)
  {dims:Fin n → ℕ}{V:Realm G ((terms grades power P).order+1) Credit.leanC}{draw:V.draws=R.family.path.levels}
  {rate allowance:ℝ}(digits:Digits V.draws (Fin n))(test:Case dims)(κ:(v:Fin n)  →  Knob (dims v))
  (pt:Fin n  →  Chamber)(seed:(v:Fin n)  →  Choice R grades v)(wallet:Wallet (room (Fin n)))


theorem original (age:ℕ)(ready:o≤age)(live:age<N)(z:Fin n → Cover)(w:Fin n→ℝ)
    (raw:Config G (R.family.side (age+1) per)→Marker.Poly (Stock.census (Fin n)))
    (entry:Registered (K:=K) (per:=per) (draw:=draw) (rate:=rate) (allowance:=allowance) power P house day
      digits test κ pt seed wallet age ready live z w raw):
    let H:=WilsonMovingForkPostedMaterial.file entry.matter wallet
    let g:=regulatorRun R.family N per (age+1)
    let b:=board H
    let bank:=value b.binder b.load b.copies g b.wallet
    Integrable raw (prior G _) ∧
    (∀U,raw U=(((R.family.path.rep N per (age+1)).eval U:ℝ):ℂ) • bank U) ∧
    ∀s:(Stock.census (Fin n)).Mode, WilsonThermometerUnitFilingCoarse.reading R (N:=N) (fun U=>(raw U).part s) (age+1) le_rfl=(polynomial H g).part s:=by
  have integrable:=WilsonOriginalRegisteredWhole.original power P house day digits test κ pt seed wallet
    age ready live z w raw entry
  obtain ⟨op,_seats,_class,sold⟩:=entry.paid
  refine ⟨integrable,?_⟩
  let sheet:=WilsonMovingForkPostedMaterial.file entry.matter wallet
  let b:=board sheet
  let g:=regulatorRun R.family N per (age+1)
  let same (f:Config G (R.family.side (age+1) per)→Marker.Poly (Stock.census (Fin n))):Prop:=
    (∀U,f U=(((R.family.path.rep N per (age+1)).eval U:ℝ):ℂ) • (value b.binder b.load b.copies g b.wallet U)) ∧
    ∀s:(Stock.census (Fin n)).Mode,WilsonThermometerUnitFilingCoarse.reading R (N:=N) (fun U=>(f U).part s) (age+1) le_rfl=
      (polynomial sheet g).part s
  change same raw
  apply (congrArg same entry.source).mpr
  exact WilsonMovingForkPostedMaterial.original (paid:=sold 1 zero_lt_one) (course:=(day.seen per).1)
    (cut:=live) (x:=wallet) ..

end YM.Integration.WilsonMovingForkRegisteredMaterial
end
