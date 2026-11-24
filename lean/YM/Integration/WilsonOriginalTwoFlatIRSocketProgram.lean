import YM.Integration.WilsonOriginalTwoFlatIRSocketSources
import YM.Integration.WilsonOriginalTwoFlatIRSocketFigure
import YM.Integration.WilsonOriginalTwoFlatIRSocketRanges
import YM.Integration.WilsonOriginalTwoFlatIRSocketBoundary
import YM.Integration.WilsonOriginalTwoFlatIRSocketVisit
import YM.Integration.WilsonOriginalTwoFlatIRSocketRose
import YM.Integration.WilsonReceivedChronologicalFixedRoseSingle
import YM.Integration.WilsonReceivedChronologicalFixedRoseAllRows
import YM.Integration.WilsonOriginalObservedRoseFittedPurse
import YM.Integration.WilsonReceivedChronologicalFixedRoseArrival
import YM.Integration.WilsonReceivedChronologicalFixedRoseBoundary
/-! The true microscopic Wilson reading is compared to the four remaining dated readings on the same signed fixed sockets. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRSocketProgram
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


open WilsonOriginalObservedRoseCorrectedWords (votes inputs)
open WilsonMeasuredPublicEntranceCellWords (submitted)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonReceivedCanonicalVersePortfolio (weight)
open WilsonReceivedChronologicalFixedSocketLife (line)
open Extraction

variable {φ:Test n}{caps:Fin n → ℝ}{A target:ℕ}{η:ℝ}
  (classroom:Purchased (per:=per) (V:=V) (draw:=draw) (rate:=rate) (allowance:=allowance) power P house day κ pt top first valid toll old φ caps A target η)
  {f request pole cards:ℕ}{B:ℝ}(fine:f ≤ top)
  (panel:Panel R grades N per f top fine valid request pole cards B)
  (file:WilsonMovingForkHeterogeneousCut.Filed R grades top)
  (s:(Stock.census (Fin n)).Mode)(testCap:∀v,‖test v‖ ≤ caps v)(hd:∀v,0 < grades v)
  (prior:Selection R grades s.val → (i:ℕ) → Config G (R.family.side i per) → Marker.Poly (Stock.census (Fin n)))
  (σ:Selection R grades s.val → ℝ)
local notation "ν" => R.family.path.rep N per top
local notation "gK" => regulatorRun R.family N per top
local notation "g₀" => regulatorRun R.family N per (first+1)
local notation "v₀" => votes R grades (N:=N) (per:=per) file panel.names panel.turn
local notation "due" => WilsonReceivedCanonicalVersePortfolio.wallet R grades
  (fun _=>B*(R.family.path.levels.clock.hatBeta top)^pole) s.val
local notation "priceₒ" => (4*((2*A:ℕ):ℝ)/Real.log 3)*wage s P 1 η*(g₀)^target
local notation "range₀" => Finset.Ico (first+1) (top-2)

local notation "bank₀" => WilsonReceivedChronologicalFixedRoseCell.bank (G:=G) (n:=n) (N:=N) (grades:=grades) (dims:=dims) (R:=R) (per:=per) (V:=V) (draw:=draw) (rate:=rate) (allowance:=allowance)
  (power:=power) (P:=P) (house:=house) (day:=day) (κ:=κ) (pt:=pt) (top:=top) (first:=first)
  (valid:=valid) (toll:=toll) (old:=old) (test:=test) (classroom:=classroom) (fine:=fine) (panel:=panel)
  (s:=s) (testCap:=testCap) (hd:=hd) (prior:=prior) (σ:=σ)



open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonMeasuredPublicEntranceCellWords (physical)
open WilsonMeasuredPublicEntrancePanel (Reading)
open RG16 RG16.Literal
open Extra.Histories Extra.Trajectories Extra.Multi


local notation "mb" => old.trans (Nat.le_succ first)

open WilsonOriginalTwoFlatIRCapturedCross (Quote)
open Planned.GuardedAtom Extra.Histories Next.Foundations RG16 RG16.Literal Trace.Physical.GermGraph
local notation "gC" z:max => regulatorRun R.family N per z
local notation "marks" => Stock.census (Fin n)
local notation "λ₀" => fun q:Selection R grades s.val=>weight R grades N per top (v₀) s.val q
local notation "gates" c:max => WilsonOriginalCensusPublicationClock.Open R simple grades (ask₀).school.pieces
  ((ask₀).school.order+1) (ask₀).load c

open WilsonOlderFreshSoftSocketRestored (degree)
open WilsonOlderFreshSoftSocketMeasuredCash (packet)
open WilsonOlderFreshSoftSocketGross (gross)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketTotal (figure)
open WilsonIndependentCollarOrdinaryCruise (address)
open WilsonOriginalTwoFlatIRSocketPower (debt)
local notation "look" => WilsonReceivedChronologicalFixedCellFee.tape (R₀:=R) (V₀:=V) (arity:=n) (K₀:=top) (per₀:=per) (f₀:=f) draw fine panel.loc
local notation "paths" => WilsonIndependentCollarDatedPrior.onLevels draw (look)
local notation "placed₀" => WilsonReceivedChronologicalMaterialLine.homes (V:=V) (look) (0:Fin n → Cover) first (first-first)
local notation "count₀" => Fintype.card (Multi.Hot (Stock.census (Fin n)))
local notation "q₀" => (terms grades power P).order

theorem original (r:ℝ)(rp:0 < r)(small:factor R φ*r ≤ R.family.S.a 0)
    (atCapture:first+1 < capture R φ r)(born:capture R φ r ≤ f)(narrow:8*R.family.S.a f < R.family.S.a (capture R φ r))
    (occurs:WilsonCenteredCompactBooking.mass R φ r (f,per) panel.loc≠0)
    (forests:∀(j:ℕ)(u:Covers R.family.path.levels.S (j+1) (coarse R (j+1) per)),Forest (step R (j+1) u.val).ratio)
    (chosen:∀(j:ℕ)(u:Covers R.family.path.levels.S (j+1) (coarse R (j+1) per)),(step R (j+1) u.val).Choices)
    {df:ℕ}{frame:Frame G df}(section_:SectionData frame)(group:Hol G)
    (station:panel.slot=file.station)(axes:panel.axis=file.A N per)

    (upper:capture R φ r < top)
    (source:Reading R grades panel ((mb).trans (atCapture.le.trans born)))
    (one:∀i,1≤panel.M i)(E:Fin n → ℕ)
    (refs:∀i j,j≤grades i → R.family.ref j≤N)
    (fare:∀i,Next.Rank.Spindle.paid R.family (grades i) f N per (panel.names i)≤panel.M i*(R.family.path.levels.clock.hatBeta f)^(E i))
    (order:ℕ)(room:order+∑i∈s.val,E i≤request)

    (young:capture R φ r<top-1)(big:2≤R.alloy.B.a.clock.hatBeta (capture R φ r))(licensed:gates (capture R φ r))
    (clocked:(eventually_atTop.mp (WilsonOriginalTwoFlatIRRows.nextClock R simple)).choose≤capture R φ r)
    {p depth E₀:ℕ}(quote:Quote R N per m (first+1) (capture R φ r) p depth ((mb).trans atCapture.le) atCapture.le)
    {C:ℝ}(cp:1≤C)(allowed:allowance≤1)(rent:0≤rate)
    (out:rate≤C*(3*(gC (capture R φ r))⁻¹)^E₀)(cap:∀a,caps a≤C*(3*(gC (capture R φ r))⁻¹)^E₀)
    {α:ℝ}(strip:(R.family.path.rep N per (capture R φ r)).p.supportExponent≤α)
    (ou:Opened R.family 0 m per)(ov:Opened R.family 0 (first+1) per)
    (reach:4*(p+(WilsonOriginalTwoFlatIRHalo.power s.val.card ((∑a,grades a)+1+2+(2+2*n*E₀))+0+2))≤depth)

    (terminalQ goal:ℕ)(cold:g₀≤1)(coldK:gK≤1){C₁:ℝ}{E₁:ℕ}(cp₁:1≤C₁)
    (out₁:rate≤C₁*(3*(g₀)⁻¹)^E₁)(inputs₁:∀a,‖test a‖≤C₁*(3*(g₀)⁻¹)^E₁)
    (kept:goal+debt n E₁ (count₀)≤terminalQ+1)(budget:terminalQ≤q₀)
    (used:s.val.Nonempty)(Vₚ:Realm G (terminalQ+1) Credit.leanC)(drawₚ:Vₚ.draws=R.family.path.levels)
    (paidₚ:Vₚ.paid=R.metals.O)(dorm:Dormitory Vₚ (mass grades s.val) 0 Credit.leanC)(origin:Vₚ.anchor≤first+1)
    (A₁ B₁:ℝ)(front:PadRank Vₚ (capture R φ r) top A₁)(march:PadRank Vₚ (first+1) (capture R φ r) B₁)
    (H:ℕ)(ranks:∀q:Selection R grades s.val,degree R grades s.val (WilsonOlderFreshSoftSocketFaces.fill R grades s.val q)≤H)
    (crop:H≤terminalQ)(kinetic:∀h≤H,WilsonOlderFreshSoftSocketFare.bracket R N per top (first+1) h terminalQ≤(g₀)^goal):
    ‖reading R (N:=N) (credit R.family N per 0 (physical R grades panel.names panel.turn panel.loc s) top valid) m
        (((mb).trans (atCapture.le.trans born)).trans fine)-
      figure R grades κ pt N per top (capture R φ r) (first+1) (paths) s.val (v₀) (WilsonIndependentCollarOrdinaryCruise.address (ι:=Fin n) R.family.path.levels (paths) ((capture R φ r)-(first+1)) (first+1) (placed₀))
        (touch test s.val) terminalQ (g₀)‖≤
      (((∏i∈s.val,WilsonAddressedHomeDose.ceiling (R:=R) (grades i) (panel.M i))*
          ((R.family.path.levels.clock.hatBeta f)^order)⁻¹+(due)*(priceₒ))+
        (due)*(WilsonOriginalTwoFlatIRSocketRose.charge R grades power P C α E₀ s*(gC (capture R φ r))^p)+
      ‖WilsonOriginalTwoFlatIRSocketBoundary.last R (N:=N) (b:=first+1) (λ₀) (bank₀) s‖+
      ‖WilsonOriginalTwoFlatIRSocketBoundary.first R (N:=N) (u:=m) (K:=top) (λ₀) (bank₀) s‖)+
      ((∑b:Columns R (fun i:s.val=>grades i),‖packet R grades s.val (v₀) N per top b‖)*
        WilsonOlderFreshSoftSocketCensus.fee R grades s.val)*
        ((g₀)^goal*(WilsonOriginalTwoFlatIRSocketPower.ceiling n (q₀) (∑a,grades a) E₁ (count₀) C₁+
          ‖touch test s.val‖*gross R dims grades terminalQ s.val A₁ B₁)):=by
  have earlier:=WilsonOriginalTwoFlatIRSocketRanges.original
    (R:=R) (per:=per) (V:=V) (draw:=draw) (rate:=rate) (allowance:=allowance) (power:=power) (P:=P)
    (house:=house) (day:=day) (κ:=κ) (pt:=pt) (top:=top) (first:=first) (valid:=valid) (toll:=toll)
    (old:=old) (test:=test) (classroom:=classroom) (fine:=fine) (panel:=panel) (file:=file)
    (s:=s) (testCap:=testCap) (hd:=hd) (prior:=prior) (σ:=σ)
    r rp small atCapture born narrow occurs forests chosen section_ group station axes upper source one E refs fare order room
    young big licensed clocked quote cp allowed rent out cap strip ou ov reach
  let reference : Selection R grades s.val := fun _=>Sum.inl ()
  let common(q:Selection R grades s.val) : (i:ℕ) → Config G (R.family.side i per) → Marker.Poly (Stock.census (Fin n)) :=
    WilsonReceivedChronologicalFixedSocketLife.line (R:=R) (per:=per) (V:=V) (draw:=draw) (rate:=rate)
      (allowance:=allowance) (power:=power) (P:=P) (house:=house) (day:=day) (κ:=κ) (pt:=pt)
      (top:=top) (first:=first) (valid:=valid) (toll:=toll) (old:=old) (test:=test) (classroom:=classroom)
      (fine:=fine) (z:=panel.loc) (s:=s) (q:=q) (paid:=testCap) (hd:=hd) (prior:=prior reference) (σ:=σ reference)
  have between:first<top-1:=by omega
  have occupied(q:Selection R grades s.val):(bank₀) q (first+1)=common q (first+1):=
    WilsonOriginalTwoFlatIRSocketSources.registered (R:=R) (per:=per) (V:=V) (draw:=draw) (rate:=rate)
      (allowance:=allowance) (power:=power) (P:=P) (house:=house) (day:=day) (κ:=κ) (pt:=pt)
      (top:=top) (first:=first) (valid:=valid) (toll:=toll) (old:=old) (test:=test) (classroom:=classroom)
      (fine:=fine) (z:=panel.loc) (s:=s) (q:=q) (paid:=testCap) (hd:=hd) (prior:=prior q) (σ:=σ q)
      first le_rfl between (prior reference) (σ reference)
  have refile:WilsonOriginalTwoFlatIRSocketBoundary.held R (N:=N) (b:=first+1) (λ₀) (bank₀) s=
      WilsonOriginalTwoFlatIRSocketBoundary.held R (N:=N) (b:=first+1) (λ₀) common s:=by
    unfold WilsonOriginalTwoFlatIRSocketBoundary.held
    exact Finset.sum_congr rfl fun q _=>by rw [occupied q]
  have later:=WilsonOriginalTwoFlatIRSocketFigure.original
    (R:=R) (per:=per) (V:=V) (draw:=draw) (rate:=rate) (allowance:=allowance) (power:=power) (P:=P)
    (house:=house) (day:=day) (κ:=κ) (pt:=pt) (top:=top) (first:=first) (valid:=valid) (toll:=toll)
    (old:=old) (test:=test) (classroom:=classroom) (fine:=fine) (z:=panel.loc) (paid:=testCap)
    (hd:=hd) (background:=prior reference) (σ:=σ reference) (labels:=v₀) (mask:=s) (j:=first)
    le_rfl (by omega) atCapture.le (born.trans fine) cold coldK cp₁ allowed rent out₁ inputs₁ terminalQ goal kept budget
    used Vₚ drawₚ paidₚ dorm origin A₁ B₁ front march H ranks crop kinetic
  refine (norm_sub_le_norm_sub_add_norm_sub _ (WilsonOriginalTwoFlatIRSocketBoundary.held R (N:=N) (b:=first+1) (λ₀) (bank₀) s) _).trans
    (add_le_add earlier ?_)
  rw [refile]
  exact later

end YM.Integration.WilsonOriginalTwoFlatIRSocketProgram
end
