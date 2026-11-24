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
namespace YM.Integration.WilsonOriginalTwoFlatIRSocketRanges
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
    (reach:4*(p+(WilsonOriginalTwoFlatIRHalo.power s.val.card ((∑a,grades a)+1+2+(2+2*n*E₀))+0+2))≤depth):
    ‖reading R (N:=N) (credit R.family N per 0 (physical R grades panel.names panel.turn panel.loc s) top valid) m
        (((mb).trans (atCapture.le.trans born)).trans fine)-
      WilsonOriginalTwoFlatIRSocketBoundary.held R (N:=N) (b:=first+1) (λ₀) (bank₀) s‖≤
      ((∏i∈s.val,WilsonAddressedHomeDose.ceiling (R:=R) (grades i) (panel.M i))*
          ((R.family.path.levels.clock.hatBeta f)^order)⁻¹+(due)*(priceₒ))+
        (due)*(WilsonOriginalTwoFlatIRSocketRose.charge R grades power P C α E₀ s*(gC (capture R φ r))^p)+
      ‖WilsonOriginalTwoFlatIRSocketBoundary.last R (N:=N) (b:=first+1) (λ₀) (bank₀) s‖+
      ‖WilsonOriginalTwoFlatIRSocketBoundary.first R (N:=N) (u:=m) (K:=top) (λ₀) (bank₀) s‖:=by
  have bochner (q:Selection R grades s.val):∀j,first+1≤j→j≤top→Integrable ((bank₀) q j) (Wilson.prior G _):=
    WilsonReceivedChronologicalFixedRoseAllRows.original (R:=R) (per:=per) (V:=V) (draw:=draw) (rate:=rate) (allowance:=allowance)
      (power:=power) (P:=P) (house:=house) (day:=day) (κ:=κ) (pt:=pt) (top:=top) (first:=first) (valid:=valid) (toll:=toll) (old:=old)
      (test:=test) (q:=q) (classroom:=classroom) (fine:=fine) (panel:=panel)
      (s:=s) (testCap:=testCap) (hd:=hd) (prior:=prior) (σ:=σ)
  have inlet:=WilsonReceivedChronologicalFixedRoseSingle.on_rows (R:=R) (per:=per) (V:=V) (draw:=draw) (rate:=rate)
    (allowance:=allowance) (power:=power) (P:=P) (house:=house) (day:=day) (κ:=κ) (pt:=pt) (top:=top)
    (first:=first) (valid:=valid) (toll:=toll) (old:=old) (test:=test) (classroom:=classroom) (fine:=fine)
    (panel:=panel) (file:=file) (s:=s) (testCap:=testCap) (hd:=hd) (prior:=prior) (σ:=σ)
    r rp small atCapture born narrow occurs forests chosen section_ group station axes upper source one E refs fare order room bochner
  let a:=capture R φ r-1
  have which:a+1=capture R φ r:=by dsimp [a];omega
  let cost:=WilsonOriginalTwoFlatIRSocketRose.charge R grades power P C α E₀ s*(gC (capture R φ r))^p
  have paid (q:Selection R grades s.val):
      ‖reading R (N:=N) (fun U=>((bank₀) q (capture R φ r) U).part s) m ((mb).trans atCapture.le)-
        reading R (N:=N) (fun U=>((bank₀) q (capture R φ r) U).part s) (first+1) atCapture.le‖≤cost:=by
    have move {F:ℕ → Prop} (h:F (capture R φ r)):F (a+1):=Eq.mp (congrArg F which.symm) h
    let quotesAt (dayIdx : ℕ) : Prop := ∀ mu : m ≤ dayIdx, ∀ vu : first + 1 ≤ dayIdx,
      Quote R N per m (first+1) dayIdx p depth mu vu
    have quoted:quotesAt (capture R φ r):=fun _ _=>@quote
    have quoteAt:quotesAt (a+1):=move quoted
    have quote₀:Quote R N per m (first+1) (a+1) p depth (by omega) (by omega):=@quoteAt _ _
    have earned:=WilsonOriginalTwoFlatIRSocketVisit.original (R:=R) (per:=per) (V:=V) (draw:=draw)
      (rate:=rate) (allowance:=allowance) (power:=power) (P:=P) (house:=house) (day:=day) (κ:=κ) (pt:=pt)
      (top:=top) (first:=first) (valid:=valid) (toll:=toll) (old:=old) (test:=test) (classroom:=classroom)
      (fine:=fine) (z:=panel.loc) (s:=s) (q:=q) (paid:=testCap) (hd:=hd) (background:=prior q) (σ:=σ q)
      (j:=a) (p:=p) (depth:=depth) (E:=E₀) (α:=α) r rp small (by omega) which.le born (by omega) narrow occurs (by simpa only [which] using big)
      (by simpa only [which] using licensed) (by simpa only [which] using clocked) (by omega) (by omega) quote₀
      cp allowed rent (by simpa only [which] using out) (by simpa only [which] using cap)
      (move (F:=fun i=>(R.family.path.rep N per i).p.supportExponent≤α) strip) ou ov reach
    let earnedAt (i:ℕ):Prop:=∀ h : m ≤ i, ∀ k : first + 1 ≤ i,
      ‖reading R (N:=N) (fun U=>((bank₀) q i U).part s) m h-
        reading R (N:=N) (fun U=>((bank₀) q i U).part s) (first+1) k‖≤
        WilsonOriginalTwoFlatIRSocketRose.charge R grades power P C α E₀ s*(gC i)^p
    have saved:earnedAt (a+1):=fun _ _=>earned.2.2
    have actual:earnedAt (capture R φ r):=Eq.mp (congrArg earnedAt which) saved
    exact actual _ _
  have span:=WilsonOriginalTwoFlatIRSocketBoundary.shifted R (N:=N) (λ₀) (bank₀) s (mb) atCapture (fun _=>cost) paid
  have purse:=WilsonOriginalObservedRoseFittedPurse.original R grades panel file station axes s
  have pos:0≤cost:=(norm_nonneg _).trans (paid (fun _=>Sum.inl ()))
  have charged:(∑q:Selection R grades s.val,‖(λ₀) q‖*cost)≤(due)*cost:=by
    rw [←Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right purse pos
  have cross:=span.trans charged
  let base:=WilsonOriginalTwoFlatIRSocketBoundary.held R (N:=N) (b:=first+1) (λ₀) (bank₀) s
  have result:=WilsonOriginalTwoFlatIRSocketBoundary.estimate R (N:=N) (K:=top) (λ₀) (bank₀) s (mb)
    atCapture _ base _ 0 _ inlet (by simp [base]) cross
  simpa only [add_zero] using result

end YM.Integration.WilsonOriginalTwoFlatIRSocketRanges
end
