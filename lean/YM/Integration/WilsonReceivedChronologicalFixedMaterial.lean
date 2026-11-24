import YM.Integration.WilsonReceivedChronologicalFixedPair
import YM.Integration.WilsonReceivedChronologicalMaterialEndpoint
import YM.Integration.WilsonOriginalOneArmMaterialGrant
/-! The purchased marked material at both ranks yields the signed earlier physical fee. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedMaterial
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
variable {G:Gauge}{n q m j N per p₀:ℕ}{grades:Fin n → ℕ}{R:Run G}{simple:G.Simple}
  {semester:WilsonOriginalAllOrderCourse.Schedule G}(house:Room semester R simple)(ask:Demand q p₀ grades)
  (day:Day semester R simple ask.school m N)(base:m ≤ j)
open WilsonReceivedChronologicalMaterialRoster (Filed)
open WilsonIndependentCollarDatedPrior (onLevels)
variable {dims:Fin n → ℕ}{V:Realm G (q+1) Credit.leanC}{draw:V.draws=R.family.path.levels}{rate allowance:ℝ}
  (digits:Digits V.draws (Fin n))(test:Case dims)(κ:(v:Fin n) → Knob (dims v))
  (pt:Fin n → Chamber)(top:ℕ)(seed:(v:Fin n) → Choice R grades v)
variable (sites:Fin n → Cover)
variable (L:Material R N (j+1) q grades ((Poetry.Agenda.seed (WilsonOriginalCensusPhysicalAttendance.roots semester R simple) MintClock.splits (Burn.horizon ask.vac)) (R.alloy.B.a.clock.J (j+1))) (binder (coarse R (j+1) per) sites))
    (U:Material R N ((j+1)+1) q grades ((Poetry.Agenda.seed (WilsonOriginalCensusPhysicalAttendance.roots semester R simple) MintClock.splits (Burn.horizon ask.vac)) (R.alloy.B.a.clock.J (j+2))) (binder (fine R (j+1) per) (chartIn (loose R.family.path.levels (j+1)) sites ((onLevels draw digits) (j+1)))))
    (low:Filed (K:=top) (draw:=draw) (rate:=rate) (δ:=allowance) digits κ pt seed (coarse R (j+1) per) sites test L)
    (high:Filed (K:=top) (draw:=draw) (rate:=rate) (δ:=allowance) digits κ pt seed (fine R (j+1) per) (chartIn (loose R.family.path.levels (j+1)) sites ((onLevels draw digits) (j+1))) test U)
    (wallet:Wallet (room (Fin n)))
    (tags:(u:Covers R.family.path.levels.S (j+1) (coarse R (j+1) per)) → (step R (j+1) u.val).Choices)
    (later:j+1 < top)(valid:top ≤ N)
variable
  (opL:Mentor.Opportunity (R.alloy.B.a.clock.J (j+1)) (R.alloy.B.a.clock.J j))
  (lessonL:Lesson (N:=N) R day.hk (WilsonOriginalCensusPhysicalAttendance.roots semester R simple) (WilsonOriginalCensusPhysicalAttendance.tab semester R simple) day.π day.Γ base)
  (opU:Mentor.Opportunity (R.alloy.B.a.clock.J (j+2)) (R.alloy.B.a.clock.J (j+1)))
  (lessonU:Lesson (N:=N) R day.hk (WilsonOriginalCensusPhysicalAttendance.roots semester R simple) (WilsonOriginalCensusPhysicalAttendance.tab semester R simple) day.π day.Γ (Nat.le_succ_of_le base))
  (tollL tollU:Fin n → ℝ){tolL tolU:ℝ}
  (lowerFile:WilsonOriginalCensusMaterialPosting.Posted R day.hk (WilsonOriginalCensusPhysicalAttendance.roots semester R simple) (WilsonOriginalCensusPhysicalAttendance.tab semester R simple) day.π day.Γ (day.Ψ per) house.books base opL lessonL house.ahead (port (coarse R (j+1) per) sites) (binder (coarse R (j+1) per) sites) grades q ask.shelf q tollL L tolL)
  (upperFile:WilsonOriginalCensusMaterialPosting.Posted R day.hk (WilsonOriginalCensusPhysicalAttendance.roots semester R simple) (WilsonOriginalCensusPhysicalAttendance.tab semester R simple) day.π day.Γ (day.Ψ per) house.books (Nat.le_succ_of_le base) opU lessonU house.ahead (port (fine R (j+1) per) (chartIn (loose R.family.path.levels (j+1)) sites ((onLevels draw digits) (j+1)))) (binder (fine R (j+1) per) (chartIn (loose R.family.path.levels (j+1)) sites ((onLevels draw digits) (j+1)))) grades q ask.shelf q tollU U tolU)

open Comparison.Density.Transport
local notation "zU" => chartIn (loose R.family.path.levels (j+1)) sites ((onLevels draw digits) (j+1))
local notation "gridᵤ" => fine R (j+1) per
local notation "gridₗ" => coarse R (j+1) per
local notation "H₁" => R.alloy.B.a.clock.hatBeta (j+1)
local notation "H₂" => R.alloy.B.a.clock.hatBeta (j+2)
local notation "clock" => R.alloy.B.a.clock
local notation "strip₀" => Poetry.Agenda.seed (WilsonOriginalCensusPhysicalAttendance.roots semester R simple) MintClock.splits (Burn.horizon ask.vac) ((clock).J (j+1))
local notation "Bᵤ" => binder (gridᵤ) (zU)
local notation "Bₗ" => binder (gridₗ) sites
local notation "hi₀" => WilsonNeutralTwoPrintPathPostedWallet.vote R day.hk (WilsonOriginalCensusPhysicalAttendance.roots semester R simple) (WilsonOriginalCensusPhysicalAttendance.tab semester R simple) day.π day.Γ (day.Ψ per) house.books
  (Nat.le_succ_of_le base) opU lessonU house.ahead (port (gridᵤ) (zU)) (Bᵤ) grades q ask.shelf q tollU U upperFile wallet
local notation "lo₀" => WilsonNeutralTwoPrintPathPostedWallet.vote R day.hk (WilsonOriginalCensusPhysicalAttendance.roots semester R simple) (WilsonOriginalCensusPhysicalAttendance.tab semester R simple) day.π day.Γ (day.Ψ per) house.books
  base opL lessonL house.ahead (port (gridₗ) sites) (Bₗ) grades q ask.shelf q tollL L lowerFile wallet
local notation "cashᵤ" v:max => tollU v*max 1 (WilsonOriginalMixedBlockBudget.roots (Bᵤ)
    (WilsonIndependentCollarMaterialWallet.bill U tollU))
local notation "cashₗ" v:max => tollL v*max 1 (WilsonOriginalMixedBlockBudget.roots (Bₗ)
    (WilsonIndependentCollarMaterialWallet.bill L tollL))

local notation "rank₀" => WilsonOriginalCensusPhysicalLoad.rank (sides grades grades)
local notation "hat₀" => R.alloy.B.a.clock.hatBeta (j+1)
local notation "money" p:max => WilsonOriginalCensusCanonicalSparseBudget.winding (hat₀) p (rank₀)
local notation "mass₀" s:max => WilsonOriginalCensusPhysicalLoad.head (sides grades grades) s



open WilsonOriginalFullRosterCouplingClock (work)
open WilsonReceivedChronologicalDualInterval (Owned)
local notation "rk₀" => (∑v:Fin n,grades v)+1
local notation "debit₀" => (((∑v:Fin n,grades v)+1+5)*Fintype.card (Fin n))
local notation "cost₀" => (2:ℝ)^(q+ask.shelf+1)
local notation "hiWord" => WilsonReceivedChronologicalMaterialEndpoint.submitted R (WilsonOriginalCensusPhysicalAttendance.roots semester R simple) (day.Ψ per)
  (port (gridᵤ) (zU)) (Bᵤ) grades q U wallet
local notation "loWord" => WilsonReceivedChronologicalMaterialEndpoint.submitted R (WilsonOriginalCensusPhysicalAttendance.roots semester R simple) (day.Ψ per)
  (port (gridₗ) sites) (Bₗ) grades q L wallet
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

include low high later valid tags upperFile lowerFile in
theorem original (sameOrder:ask.order=q)(p:ℕ)
    (demand:WilsonOriginalCensusPublicationClock.Load ask.vac q q ask.shelf p₀ grades ask.school.pieces (ask.school.order+1))
    (enrolled:q ≤ Burn.horizon ask.vac+1)(sized:q ≤ (clock).J (j+1))
    (below:WilsonOriginalCensusPublicationClock.Open R simple grades ask.school.pieces (ask.school.order+1) demand j)
    (above:WilsonOriginalCensusPublicationClock.Open R simple grades ask.school.pieces (ask.school.order+1) demand (j+1))
    (loSeats:opL.count=ask.school.pieces)(hiSeats:opU.count=ask.school.pieces)
    (ready:WilsonReceivedMeasuredStampPrice.opening R simple (p₀+1) q ask.vac demand.deep demand.aged
      (by positivity:0<(1:ℝ)) ≤ j+1)
    (paidAge:(eventually_atTop.mp (WilsonEmittedOriginalCalendar.wages R simple)).choose ≤ j+1)
    (charge:Fin n→ℕ)(up:∀v,cashᵤ v ≤ (H₂)^(charge v))(down:∀v,cashₗ v ≤ (H₁)^(charge v))
    (early:(H₂)≤(H₁)^2)(small:tolU ≤ (Pert.Asymptotics.regulatorRun R.family N per (j+2))^(p₀+1))
    (tube:LinkTube G)(front:Multi.Hot (Stock.census (Fin n)) → Fin n)
    (owned:∀s,front s∈s.val.val)
    (teacher:0<strip₀ ∧ Real.exp ((strip₀)⁻¹^2)≤(H₁) ∧
      (((day.Ψ per) (j+1)).p.supportExponent+2)*((((day.Ψ per) (j+1)).p.B:ℝ)⁻¹)≤(strip₀)/2 ∧
      (Real.sqrt ((day.Ψ per) (j+1)).beta)⁻¹≤1/2 ∧ ((day.Ψ per) (j+1)).p.B=Nat.ceil ((Real.log (H₁))^2) ∧
      ((day.Ψ per) (j+1)).p.supportExponent+2≤102)
    {quiet:ℕ → SeriesA G}(read:Read R N m (Burn.horizon ask.vac) quiet day.π day.Γ){τ cash:ℝ}
    (funded:Issued R N ((j+1)+1) (Burn.horizon ask.vac) (quiet ((j+1)+1)) τ cash)
    (legalU:Legal (AllOrder.Floe.Step.tape (Burn.horizon ask.vac+2)) (day.π ((j+1)+1)))
    (legalL:Legal (AllOrder.Floe.Step.tape (Burn.horizon ask.vac+2)) (day.π (j+1)))
    (rates:WilsonOriginalCensusDatedHeldTariff.Rates R grades κ pt (j+1) top q)
    (within:WilsonOriginalCensusFaceAdmission.housed sites R (j+1) per)
    (target:ℕ)(enough:2*(p+1) ≤ target)
    (ceiling:3*WilsonOriginalFullRosterBookedHearing.roof grades grades (fun v=>2*charge v) target ≤ q)
    (late:WilsonOriginalCensusSparseRosterOpening.first R simple tube grades grades (fun v=>2*charge v) q q target p enough ≤ j+1)
    (gross:ℝ)(weight:∀s:YM.Multi.Hot (Stock.census (Fin n)),‖∏w∈s.val.val,(wallet w).val‖*‖touch test s.val.val‖ ≤ gross)
    (opened:∀(s:YM.Multi.Hot (Stock.census (Fin n)))(v:Fin (q+1)),WilsonOriginalCensusDatedPeriodOpening.Opened R (j+1) per
      (mass grades s.val.val+v.val) (rates.width s.val.val v) (rates.fare s.val.val v) gross (money p))
    (C:Fin n → ℝ)(paid:∀v,‖test v‖ ≤ C v)
    (diameter:ℕ)(covered:2*((univ:Finset (Fin n)).image sites).sup WilsonNeutralTwoPrintPathBoxHome.radius ≤ diameter)
    (selected:(u:Covers R.family.path.levels.S (j+1) (coarse R (j+1) per)) → Forest (step R (j+1) u.val).ratio)
    (credit:∀s:YM.Multi.Hot (Stock.census (Fin n)),WilsonOriginalCensusMeasuredStation.CreditAt R κ pt grades C (j+1) top q per diameter
      (((hat₀)^(near (p+1) (mass₀ s.val) 1))⁻¹))
    (lawU:rows (j+2)=hiWord)(lawL:rows (j+1)=loWord)(uPos:∀v,0≤tollU v)(lPos:∀v,0≤tollL v)
    {df:ℕ}{frame:Frame G df}(section_:SectionData frame)(group:Hol G)
    {b u:ℕ}(fixed:WilsonSingleHardRadius.first R simple ≤ m)(mu:m ≤ u)(ub:u ≤ b)(bj:b ≤ j)
    (np:0<n)(P cost hardOrder size:ℕ)(tol η:ℝ)(tp:0<tol)(ep:0<η)(s:(Stock.census (Fin n)).Mode)
    (c₂:2 ≤ cost₀)
    (clockPaid:(eventually_atTop.mp (WilsonReceivedChronologicalPanelClock.original R simple ask (fun v=>2*charge v)
      P cost hardOrder target (cost₀) tol η c₂ tp ep)).choose ≤ b)
    (aperture:R.family.S.a b/R.family.S.a top ≤ (R.family.path.levels.clock.hatBeta b)^cost)
    (cashPaid:work n P (fare grades (fun v=>2*charge v)) (rk₀)+1+
      (WilsonOriginalFullRosterCouplingClock.wallet (fare grades (fun v=>2*charge v))).pole+1 ≤ p₀+1)
    (windingRank:work n P (fare grades (fun v=>2*charge v)) (rk₀)+1+1 ≤ p)
    (hardRank:work n P (fare grades (fun v=>2*charge v)) (rk₀)+2 ≤ hardOrder)
    (support:∀i,(R.family.path.levels.budget i).supportExponent=100)
    (Z:Support (R.family.side b per))(center:Site (R.family.side b per))(held:center∈Z)
    (homes:∀v∈s.val,WilsonOriginalOccupiedCorridor.sites R
      (((port (gridᵤ) (zU)).coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin)
        (by omega:b ≤ j+1) v∈Z)(roof:coverNumber (day.Ψ per b).p.B Z ≤ size):
    Owned (N:=N) R simple day.hk (WilsonOriginalCensusPhysicalAttendance.roots semester R simple) (WilsonOriginalCensusPhysicalAttendance.tab semester R simple) day.π day.Γ (day.Ψ per) house.books house.ahead rows j u b s P size η ∧
    ∀v:ℕ,u ≤ v → v ≤ b →
      WilsonReceivedChronologicalLastFlat.Ticket (N:=N) R simple day.hk (WilsonOriginalCensusPhysicalAttendance.roots semester R simple) (WilsonOriginalCensusPhysicalAttendance.tab semester R simple) day.π day.Γ (day.Ψ per) house.books house.ahead rows j u b v s P size η ∧
      ‖WilsonOriginalJointTrialHearing.fee R N per (1:Config G (R.family.side v per)) rows (j+1) s‖ ≤
        WilsonReceivedChronologicalLastFlat.wage s P size η*(Pert.Asymptotics.regulatorRun R.family N per b)^P:=by
  have purchase:=WilsonOriginalOneArmMaterialGrant.original
    (R:=R) (hk:=day.hk) (D:=WilsonOriginalCensusPhysicalAttendance.roots semester R simple)
    (Q:=WilsonOriginalCensusPhysicalAttendance.tab semester R simple) (π:=day.π) (Γ:=day.Γ) (Ψ:=day.Ψ per)
    (course:=(day.seen per).1) (books:=house.books) (base:=base) (ahead:=house.ahead)
    (digits:=digits) (test:=test) (κ:=κ) (pt:=pt) (top:=top) (seed:=seed) (sites:=sites) (L:=L) (U:=U)
    (low:=low) (high:=high) (wallet:=wallet) (tags:=tags) (later:=later) (valid:=valid)
    (shelf:=ask.shelf) (opL:=opL) (lessonL:=lessonL) (opU:=opU) (lessonU:=lessonU)
    (tollL:=tollL) (tollU:=tollU) (upperFile:=upperFile) (lowerFile:=lowerFile)
    simple (p₀+1) p ask.school.pieces (ask.school.order+1) p₀ demand enrolled demand.deep demand.aged sized
    below above loSeats hiSeats ready paidAge charge up down early small tube front owned teacher house.pass house.month
    read funded legalU legalL rates within target enough ceiling late gross weight opened C paid diameter covered selected credit
  have hv:=(upperFile.choose_spec.2.2.2.2.2.2.2.2.2 wallet).choose_spec
  have lv:=(lowerFile.choose_spec.2.2.2.2.2.2.2.2.2 wallet).choose_spec
  change (hi₀).x=wallet ∧ _ at hv
  change (lo₀).x=wallet ∧ _ at lv
  have placed:(hi₀).post.passport=port (gridᵤ) (zU):=hv.2.2.2.2.2.2.2.1
  exact WilsonReceivedChronologicalFixedPair.original ask house day base rows (hiWord) (loWord) (hi₀) (lo₀)
    s (fun v=>2*charge v) P cost hardOrder target p (p₀+1) size (cost₀) tol η c₂ tp ep clockPaid
    fixed mu ub bj later valid aperture np (fun v=>mul_nonneg (uPos v) (zero_le_one.trans (le_max_left _ _)))
    (fun v=>mul_nonneg (lPos v) (zero_le_one.trans (le_max_left _ _))) hv.2.1 lv.2.1
    (hv.2.2.1.trans sameOrder.symm) hv.2.2.2.1 (hv.2.2.2.2.1.trans hiSeats)
    tube front purchase lawU lawL cashPaid windingRank hardRank support section_ group Z center held
    (by simpa only [placed] using homes) roof
end YM.Integration.WilsonReceivedChronologicalFixedMaterial
end
