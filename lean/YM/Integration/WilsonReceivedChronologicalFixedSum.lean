import YM.Integration.WilsonReceivedChronologicalFixedMonth
import YM.Integration.WilsonReceivedChronologicalFixedEnrollment
import YM.Integration.WilsonReceivedChronologicalFixedSites
/-! Sum the actual signed chronological errors on one elected field, with the older stop chosen separately at every date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedSum
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
include valid in
theorem original {Z₀:ℕ → SeriesA G}{price:Credit}(quiet:QuietAt day price Z₀)
    (old:m ≤ first)(registered:∀i:ℕ,∀h:i∈Ico first (top-1),Nonempty (Registered (K:=top) (per:=per) (draw:=draw)
      (rate:=rate) (allowance:=allowance) power P house day digits test κ pt seed wallet i (old.trans (mem_Ico.mp h).1)
      (by have lt:=(mem_Ico.mp h).2;omega) (loc i) (toll i) (rows (i+1))))
    {Types:Type}[Fintype Types]{purchased pieces physical:ℕ}{pole:Bool → ℕ}{span:Types → ℕ}{lag:Types → Bool → ℕ}
    (tube:LinkTube G)(front:Multi.Hot (Stock.census (Fin n)) → Fin n)(member:∀s,front s∈s.val.val)
    (faculty:∀j≥first,WilsonIndependentCollarDatedTeachers.At schedule R simple V dims grades (Burn.horizon (ask₀).vac)
      purchased allowance tube pieces physical pole span lag j)(anchor:V.anchor ≤ first)
    (sparse:WilsonOriginalCensusSparseRosterOpening.first R simple tube grades grades (charges power)
      (bill₀).order (bill₀).order (bill₀).target (bill₀).precision (bill₀).enough ≤ first)

    {u b:ℕ}(past:first ≤ b)(inside:b ≤ top)(mu:m ≤ u)(ub:u ≤ b)
    (caps:Fin n → ℝ)(paid:∀v,‖test v‖ ≤ caps v)
    (period:∀j∈Ico b (top-2),Nonempty (Sheets (R:=R) (per:=per) (V:=V) (grades:=grades) (j:=j)
      power P digits κ pt top first caps))
    (forests:∀(j:ℕ)(u:Covers R.family.path.levels.S (j+1) (coarse R (j+1) per)),Forest (step R (j+1) u.val).ratio)
    (chosen:∀(j:ℕ)(u:Covers R.family.path.levels.S (j+1) (coarse R (j+1) per)),(step R (j+1) u.val).Choices)
    {df:ℕ}{frame:Frame G df}(section_:SectionData frame)(group:Hol G)
    (fixed:WilsonSingleHardRadius.first R simple ≤ m)(np:0 < n)(cost:ℕ)(tol η:ℝ)(tp:0 < tol)(ep:0 < η)
    (bought:start grades power P R simple cost tol η tp ep ≤ b)
    (aperture:R.family.S.a b/R.family.S.a top ≤ (R.family.path.levels.clock.hatBeta b)^cost)
    (support:∀i,(R.family.path.levels.budget i).supportExponent=100)
    (housing:∀j,∀h:j∈Ico b (top-2),
      let y:=homes digits (0:Fin n → Cover) first (j-first)
      let high:=chartIn (loose R.family.path.levels (j+1)) y ((onLevels draw digits) (j+1))
      let port₀:=port (fine R (j+1) per) high
      ∀v:Fin n,WilsonOriginalOccupiedCorridor.sites R (port₀.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
        (by have earlier:=(mem_Ico.mp h).1;omega:b ≤ j+1) v∈({0}:Support (R.family.side b per)))
    (clocked:(WilsonReceivedChronologicalDates.stages R simple cost).choose ≤ b)(target:ℕ)(extra:P=target+1):
    (∀j∈Ico b (top-2),∀s:(Stock.census (Fin n)).Mode,
      Owned (N:=N) R simple day.hk (roots₀) (tab₀) day.π day.Γ (day.Ψ per) house.books house.ahead rows j u b s P 1 η ∧
      ∀v:ℕ,u ≤ v → v ≤ b → Ticket (N:=N) R simple day.hk (roots₀) (tab₀) day.π day.Γ (day.Ψ per) house.books
        house.ahead rows j u b v s P 1 η) ∧
    ∀(s:(Stock.census (Fin n)).Mode)(stop:ℕ → ℕ), (∀j∈Ico b (top-2),u ≤ stop j ∧ stop j ≤ b) →
      ∑j∈Ico b (top-2),‖fee R N per (1:Config G (R.family.side (stop j) per)) rows (j+1) s‖ ≤
        (4*(cost:ℝ)/Real.log 3)*wage s P 1 η*(gAt b)^target:=by
  let dates:=Ico b (top-2)
  have earned (j:ℕ)(h:j∈dates):∀s:(Stock.census (Fin n)).Mode,
      Owned (N:=N) R simple day.hk (roots₀) (tab₀) day.π day.Γ (day.Ψ per) house.books house.ahead rows j u b s P 1 η ∧
      ∀v:ℕ,u ≤ v → v ≤ b → Ticket (N:=N) R simple day.hk (roots₀) (tab₀) day.π day.Γ (day.Ψ per) house.books
        house.ahead rows j u b v s P 1 η ∧
        ‖fee R N per (1:Config G (R.family.side v per)) rows (j+1) s‖ ≤ wage s P 1 η*(gAt b)^P:=by
    have hj:=mem_Ico.mp h
    have early:first ≤ j:=past.trans hj.1
    obtain ⟨board⟩:=period j h
    exact WilsonReceivedChronologicalFixedMonth.original (R:=R) (simple:=simple) (schedule:=schedule) (V:=V) (draw:=draw)
      (rate:=rate) (allowance:=allowance) (power:=power) (P:=P) (house:=house) (day:=day) (first:=first)
      (digits:=digits) (test:=test) (κ:=κ) (pt:=pt) (top:=top) (seed:=seed) (wallet:=wallet) (tags:=chosen j)
      (early:=early) (live:=by omega) (valid:=valid) (rows:=rows) (toll:=toll) quiet old registered
      tube front member (faculty j early) (by omega) (by omega) caps paid board (forests j) section_ group fixed mu ub
      hj.1 np cost 1 tol η tp ep bought aperture support {0} 0 (mem_singleton_self _) (housing j h)
      (by
        let B:=(day.Ψ per b).p.B
        exact (Corona.cover_mono (Lattice.halo_subset 0 ({0}:Support (R.family.side b per))) B).trans
          (show coverNumber B (halo 0 {0}:Support (R.family.side b per)) ≤ 1 from by
            simpa using Corona.tile (0:Site (R.family.side b per)) 0 B (day.Ψ per b).p.B_pos))
  constructor
  · intro j h s
    exact ⟨(earned j h s).1,fun v hv vb=> ((earned j h s).2 v hv vb).1⟩
  intro s stop bounded
  have finish:b+(top-b)=top:=Nat.add_sub_of_le inside
  have count:=((WilsonReceivedChronologicalDates.stages R simple cost).choose_spec (N:=N) (per:=per) (b:=b) (L:=top-b)
    clocked (by simpa only [finish] using valid) (by simpa only [finish] using aperture) dates
    (fun j hj=>le_trans (mem_Ico.mp hj).1 (Nat.le_succ _))
    (fun j hj=>by have lt:=(mem_Ico.mp hj).2;omega)).1
  let w:=wage s P 1 η
  have wp:0 ≤ w:=WilsonReceivedChronologicalLastFlat.nonneg s P 1 η ep.le
  calc
    _ ≤ ∑_j∈dates,w*(gAt b)^P:=Finset.sum_le_sum fun j hj=>
      ((earned j hj s).2 (stop j) (bounded j hj).1 (bounded j hj).2).2
    _ = ((dates.card:ℝ)*(gAt b))*(w*(gAt b)^target):=by rw [Finset.sum_const,nsmul_eq_mul,extra,pow_succ];ring
    _ ≤ (4*(cost:ℝ)/Real.log 3)*(w*(gAt b)^target):=mul_le_mul_of_nonneg_right count.2.2
      (mul_nonneg wp (pow_nonneg count.1.le _))
    _ = _:=by ring
end YM.Integration.WilsonReceivedChronologicalFixedSum
end
