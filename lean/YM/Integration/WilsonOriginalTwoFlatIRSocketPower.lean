import YM.Integration.WilsonOriginalTwoFlatIRSocketTerminal
import YM.Integration.WilsonOriginalTwoFlatIRFlatWageCap
import YM.Integration.WilsonOriginalTwoFlatIRRegisteredTerminal
import YM.Integration.WilsonOriginalTwoFlatIRFixedPorts
import YM.Integration.WilsonOriginalTwoFlatIRSocketHome
import YM.Integration.WilsonReceivedChronologicalFixedSocketLife
/-! Price each genuine planted socket of the nonzero separated cell at both
held stops, on the same source as its cutoff and chronological postings. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRSocketPower
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


open WilsonReceivedChronologicalFixedEarner (programme start)
open WilsonReceivedChronologicalFixedLedger (Registered)
open WilsonReceivedChronologicalMaterialLine (homes)
variable {G:Gauge}{n m j N per:ℕ}{grades:Fin n → ℕ}{R:Run G}{simple:G.Simple}
  {schedule:WilsonOriginalAllOrderCourse.Schedule G}(power:Fin n → ℕ)(P:ℕ)
  (house:Room (prepared schedule) R simple)(day:Day (prepared schedule) R simple (programme grades power P).school m N)
  (base:m ≤ j)
open WilsonReceivedChronologicalMaterialRoster (Filed)
open WilsonIndependentCollarDatedPrior (onLevels)
variable {dims:Fin n → ℕ}{V:Realm G ((WilsonReceivedChronologicalFixedReserve.terms grades power P).order+1) Credit.leanC}{draw:V.draws=R.family.path.levels}{rate allowance:ℝ}
  (digits:Digits V.draws (Fin n))(test:Case dims)(κ:(v:Fin n) → Knob (dims v))
  (pt:Fin n → Chamber)(top:ℕ)(seed:(v:Fin n) → Choice R grades v)

variable (ground:Fin n → Cover)(first:ℕ)(early:first ≤ j)
local notation "loc" a:max => homes digits (0:Fin n → Cover) first ((a)-first)
local notation "location₀" => loc j
variable (wallet:Wallet (room (Fin n)))
  (tags:(u:Covers R.family.path.levels.S (j+1) (coarse R (j+1) per)) → (step R (j+1) u.val).Choices)
  (live:j+3 ≤ top)(valid:top ≤ N)
local notation "zU" => chartIn (loose R.family.path.levels (j+1)) location₀ ((onLevels draw digits) (j+1))
local notation "gridᵤ" => fine R (j+1) per
local notation "gridₗ" => coarse R (j+1) per
local notation "H₁" => R.alloy.B.a.clock.hatBeta (j+1)
local notation "H₂" => R.alloy.B.a.clock.hatBeta (j+2)
local notation "clock" => R.alloy.B.a.clock
local notation "strip₀" => Poetry.Agenda.seed (WilsonOriginalCensusPhysicalAttendance.roots (WilsonOriginalOpticalSchedule.prepared schedule) R simple) MintClock.splits (Burn.horizon (programme grades power P).vac) ((clock).J (j+1))
local notation "Bᵤ" => binder (gridᵤ) (zU)
local notation "Bₗ" => binder (gridₗ) location₀
local notation "rank₀" => WilsonOriginalCensusPhysicalLoad.rank (sides grades grades)
local notation "hat₀" => R.alloy.B.a.clock.hatBeta (j+1)
local notation "money" p:max => WilsonOriginalCensusCanonicalSparseBudget.winding (hat₀) p (rank₀)
local notation "mass₀" s:max => WilsonOriginalCensusPhysicalLoad.head (sides grades grades) s



open WilsonOriginalFullRosterCouplingClock (work)
open WilsonReceivedChronologicalDualInterval (Owned)
open WilsonReceivedChronologicalFixedReserve (terms charges)
local notation "bill₀" => terms grades power P
local notation "ask₀" => programme grades power P
local notation "rk₀" => (∑v:Fin n,grades v)+1
local notation "debit₀" => (((∑v:Fin n,grades v)+1+5)*Fintype.card (Fin n))
local notation "cost₀" => (2:ℝ)^((WilsonReceivedChronologicalFixedReserve.terms grades power P).order+(programme grades power P).shelf+1)
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

variable (rows:(i:ℕ) → Config G (R.family.side i per) → Marker.Poly (Stock.census (Fin n)))




open WilsonReceivedChronologicalMaterialApertures (spread diameter)
open WilsonReceivedChronologicalFixedTariff (gross)

open WilsonReceivedChronologicalFixedMonth (Sheets)
open WilsonReceivedChronologicalLastFlat (Ticket wage)
open WilsonOriginalJointTrialHearing (fee)
variable (toll:ℕ → Fin n → ℝ)
local notation "roots₀" => WilsonOriginalCensusPhysicalAttendance.roots (prepared schedule) R simple
local notation "tab₀" => WilsonOriginalCensusPhysicalAttendance.tab (prepared schedule) R simple
local notation "gAt" b:max => regulatorRun R.family N per b


open Function Set Filter MeasureTheory Analysis Table Spec Extraction Next.UVStress
open StressFlux.Matching Cells WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking
open WilsonReceivedChronologicalMaterialCapture (placed)
open WilsonReceivedChronologicalFixedEnrollment (Cohort)
open WilsonReceivedChronologicalFixedProgram (printed)
open WilsonReceivedChronologicalFixedPorts (Period)
open WilsonReceivedChronologicalFixedCohortFee (Earned)


open WilsonReceivedChronologicalFixedCellFee (factor positive capture tape)

variable (old:m ≤ first)


open WilsonReceivedChronologicalFixedPlaced (Purchased)
open WilsonReceivedChronologicalSocket (extend lit input)
open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonReceivedCanonicalVersePosterior (word)

variable {φ:Test n}{caps:Fin n → ℝ}{A target:ℕ}{η:ℝ}
  (classroom:Purchased (per:=per) (V:=V) (draw:=draw) (rate:=rate) (allowance:=allowance) power P house day κ pt top first valid toll old φ caps A target η)
  {f:ℕ}(fine:f ≤ top)(z:Sites R (f,per) n)(s:(Stock.census (Fin n)).Mode)(q:Selection R grades s.val)
  (paid:∀v,‖test v‖ ≤ caps v)(hd:∀v,0 < grades v)
  (background:(i:ℕ) → Config G (R.family.side i per) → Marker.Poly (Stock.census (Fin n)))(σ:ℝ)

local notation "cells₀" => tape draw fine z
local notation "seed₀" => extend R grades s.val q
local notation "ν" => R.family.path.rep N per top
local notation "gK" => regulatorRun R.family N per top
local notation "purchase" => classroom f fine z (seed₀) test paid
local notation "other₀" => Function.update background top (input R grades s q hd (placed R fine z) σ (ν) (gK))
local notation "x₀" => (WilsonReceivedChronologicalSocket.lit (V:=Fin n))

local notation "rows₀" => WilsonReceivedChronologicalFixedSocketLife.line (R:=R) (per:=per) (V:=V) (draw:=draw) (rate:=rate) (allowance:=allowance)
  (power:=power) (P:=P) (house:=house) (day:=day) (κ:=κ) (pt:=pt) (top:=top) (first:=first)
  (valid:=valid) (toll:=toll) (old:=old) (test:=test) (classroom:=classroom) (fine:=fine) (z:=z)
  (s:=s) (q:=q) (paid:=paid) (hd:=hd) (prior:=background) (σ:=σ)

open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFlatTelescope
open Planned.GuardedAtom Extra.Histories Next.Foundations RG16 RG16.Literal Trace.Physical.GermGraph
open WilsonOriginalTwoFlatIRCapturedCross (Quote)
open Pert.Asymptotics
local notation "X₀" => (3*(regulatorRun R.family N per (j+1))⁻¹)
local notation "rep" => R.family.path.rep N per (j+1)
local notation "marks" => Stock.census (Fin n)
local notation "gates" => WilsonOriginalCensusPublicationClock.Open R simple grades (ask₀).school.pieces
  ((ask₀).school.order+1) (ask₀).load (j+1)


open WilsonOriginalTwoFlatIRFlatMarked (seat)
local notation "q₀" => (terms grades power P).order
open WilsonOriginalTwoFlatIRFlatPaidParts (wage)
open WilsonOriginalTwoFlatIRFlatEarned (whole)
local notation "g₀" => regulatorRun R.family N per (j+1)
local notation "house₀" => homes (cells₀) 0 first (j-first)
local notation "pass₀" => port (R.family.side (j+1) per) (house₀)
local notation "bind₀" => binder (R.family.side (j+1) per) (house₀)
local notation "src₀" => (purchase).choose.choose

local notation "count₀" => Fintype.card (Multi.Hot (Stock.census (Fin n)))
def debt (n E count:ℕ):ℕ:=(2+2*n*E)*count
def ceiling (n Q h E count:ℕ)(C:ℝ):ℝ:=
  (1+WilsonOriginalTwoFlatIRFlatWageCap.cap n Q h C)^count*3^(debt n E count)

/-- The input salaries are bought on the real roster. The Laurent exponent used to choose
    the retained order is independent of that order. -/
theorem original (active:first≤j)(young:j<top-1){c:ℕ}(before:j+1≤c)(ck:c≤top)(cold:g₀≤1)
    {C:ℝ}{E:ℕ}(cp:1≤C)(allow:allowance≤1)(rp:0≤rate)(rent:rate≤C*(3*(g₀)⁻¹)^E)
    (inputs:∀a,‖test a‖≤C*(3*(g₀)⁻¹)^E)(p goal:ℕ)(kept:goal+debt n E (count₀)≤p+1)(order:p≤q₀):
    ‖(((R.family.path.rep N per (j+1)).eval 1:ℂ)⁻¹*((rows₀) (j+1) 1).part s)-
      whole (R:=R) (N:=N) (K:=top) (c:=c) (j:=j) (draw:=draw) κ pt (cells₀) (seed₀) (house₀) test
        (fun a=>((x₀) a).val) (g₀) p s.val‖ ≤ceiling n (q₀) (∑a,grades a) E (count₀) C*(g₀)^goal:=by
  let a:↥(Finset.Ico first (top-1)):=⟨j,Finset.mem_Ico.mpr ⟨active,young⟩⟩
  obtain ⟨reg,source⟩:=WilsonReceivedChronologicalFixedSocketLife.atDate (R:=R) (per:=per) (V:=V) (draw:=draw) (rate:=rate)
    (allowance:=allowance) (power:=power) (P:=P) (house:=house) (day:=day) (κ:=κ) (pt:=pt) (top:=top) (first:=first)
    (valid:=valid) (toll:=toll) (old:=old) (test:=test) (classroom:=classroom) (fine:=fine) (z:=z)
    (s:=s) (q:=q) (paid:=paid) (hd:=hd) (prior:=background) (σ:=σ) a

  have heard:=(WilsonOriginalTwoFlatIRSocketTerminal.original (G:=G) (n:=n) (N:=N) (grades:=grades) (dims:=dims)
    (R:=R) (per:=per) (V:=V) (draw:=draw) (rate:=rate) (allowance:=allowance) (power:=power) (P:=P) (house:=house)
    (day:=day) (κ:=κ) (pt:=pt) (top:=top) (first:=first) (valid:=valid) (toll:=toll) (old:=old) (test:=test)
    (classroom:=classroom) (fine:=fine) (z:=z) (s:=s) (q:=q) (paid:=paid) (hd:=hd)
    (background:=background) (σ:=σ) active young before ck cold p order).2
  have bounds:=WilsonOriginalTwoFlatIRRosePower.clock (R:=R) per (before.trans (ck.trans valid))
  have accounts:=WilsonOriginalTwoFlatIRFlatWageCap.original κ pt (cells₀) (seed₀) (house₀) test reg.matter reg.filed
    bounds.1 cp (R.alloy.B.a.fits.delayed _).le bounds.2 allow rp rent inputs
  rw [source] at accounts
  have gp:0<g₀:=ActualRunKernelPackets.regulator_pos R N per (j+1) (before.trans (ck.trans valid))
  let A₀:ℝ:=(1+WilsonOriginalTwoFlatIRFlatWageCap.cap n (q₀) (∑a,grades a) C)^(count₀)
  have ad:0≤A₀:=by dsimp [A₀,WilsonOriginalTwoFlatIRFlatWageCap.cap];positivity
  have discount:=WilsonOriginalTwoFlatIRFlatWageCap.discount (a:=A₀) gp cold ad kept
  apply heard.trans
  apply le_trans _ discount
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg gp.le _)
  have identity (b:Multi.Hot (Stock.census (Fin n))):
      ((binder (R.family.side (j+1) per) (house₀) b).mode).val=b.val.val:=rfl
  simpa [WilsonOriginalTwoFlatIRFlatPaidParts.wage,WilsonReceivedChronologicalSocket.lit,A₀,debt,identity] using accounts

end YM.Integration.WilsonOriginalTwoFlatIRSocketPower
end
