import YM.Integration.WilsonOriginalOneArmOpticalDates
import YM.Integration.WilsonOriginalCensusPublicationClock

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalOneArmBoardPair
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

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m j N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀i,RG.Rep G (R.family.side i per))
  {φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)(base:m ≤ j)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  {V:Type}[Fintype V][DecidableEq V]
local notation "marks" => Stock.census V
local notation "actors" => WilsonOriginalMixedBlockRows.room V
local notation "nulls" => fun _:V => (⊥:Submodule ℝ ℂ)
variable {S S': V → ℝ}{a a':ℕ}
variable (rows:∀i:ℕ,Config G (R.family.side i per) → Marker.Poly (Stock.census V))
variable {incomingHigh:Config G (R.family.side (j+1+1) per)→Marker.Poly (Stock.census V)}
  {incomingLow:Config G (R.family.side (j+1) per)→Marker.Poly (Stock.census V)}
variable (upper:WilsonOriginalDatedCensusInput.Filed (i:=j+1) (N:=N) R hk D Q π Γ Ψ books (Nat.le_succ_of_le base) ahead S a incomingHigh)
  (lower:WilsonOriginalDatedCensusInput.Filed (i:=j) (N:=N) R hk D Q π Γ Ψ books base ahead S' a' incomingLow)
local notation "high" => upper.post
local notation "low" => lower.post
local notation "vac" => Ψ (j+1)
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books (Nat.le_succ_of_le base)
  (high).op (high).lesson ahead (actors) (high).model upper.order (high).voter
local notation "ζ" => Oak.grade0 R hk D Q π Γ (Nat.le_succ_of_le base) (high).lesson
local notation "stamped" => Mutation.stamp (student) (Γ (j+1)) (ζ) (Burn.horizon k+2) upper.order
local notation "home" => ((high).passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
local notation "gc" => Coat.gStep (vac).beta
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1))
local notation "H" => R.alloy.B.a.clock.hatBeta (j+1)
local notation "nh" => ((∑v:V,upper.grades v)+1+5)*Fintype.card V
local notation "nl" => ((∑v:V,lower.grades v)+1+5)*Fintype.card V
local notation "fee" c:max t:max => WilsonOriginalCensusPostedWages.debit (max (nh) (nl)) c t
local notation "rank" => max ((∑v:V,upper.grades v)+1) ((∑v:V,lower.grades v)+1)

open WilsonOriginalOccupiedWindow WilsonOriginalJointTrialHearing
local notation "gf" => Coat.gStep (Ψ (j+1+1)).beta
local notation "carried" => Mutation.grow (student) (Γ (j+1)) (ζ) (Burn.horizon k+2) upper.order
  (gf) (gc) (vac) (high).output
local notation "fig" => Oak.figureReal R hk D Q π Γ books (Nat.le_succ_of_le base) (high).op (high).lesson ahead upper.order upper.shelf
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books (Nat.le_succ_of_le base)
  (high).op (high).lesson ahead upper.order upper.shelf
local notation "w₂" => Stoop.radius (high).w ((Ω)^6)


open WilsonOriginalFullRosterCouplingClock (work)
local notation "WD" f:max => WilsonOriginalFullRosterCouplingClock.wallet f
local notation "RD" d:max => WilsonOriginalFullRosterCouplingClock.raw d
local notation "DD" f:max d:max => WilsonOriginalFullRosterCouplingClock.debt f d
local notation "gAt" i:max => regulatorRun R.family N per i
local notation "ready" l:max => WilsonMeasuredSemesterSubpower.onset R l (by norm_num:0<(1:ℝ))
open private relative from YM.Integration.WilsonMeasuredImpulseCalendar
open private total from YM.Integration.WilsonOriginalCensusFiledPhysicalEdge

open WilsonOriginalOneArmClearCash (Owned)
open WilsonOriginalOneArmClearInstallment (Sale)
open WilsonOriginalCensusPublicationClock (Load Open)

/-- Equality at the two actual dates suffices to read this pair on the entire
chronological word. The regular order and the occupied fee have their own clocks. -/
theorem original {s:(marks).Mode}{charges:V→ℕ}{q target level:ℕ}{C:ℝ}
    (up:rows (j+1+1)=incomingHigh)(down:rows (j+1)=incomingLow)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(live:j+1<N)
    (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)(nn:∀v,0 ≤ S v)(nn':∀v,0 ≤ S' v)
    (calendar:WilsonOriginalSparseCensusEdge.Calendar R simple hk D Q π Γ Ψ books base ahead
      incomingHigh incomingLow upper lower charges q 1 (((H)^level)⁻¹) C)
    (seen:∀t:Hot (marks),t.val.val ⊆ s.val → WilsonOriginalSparseCensusEdge.Face R hk D Q π Γ Ψ books
      base ahead incomingHigh incomingLow upper lower t (calendar.front t) charges calendar.tube target (((H)^level)⁻¹))
    (atStation:WilsonOriginalFullRosterDatedReturn.station R simple
      (WilsonOriginalFullRosterBookedHearing.roof upper.grades lower.grades charges target) (Fintype.card V) ≤ j)
    {df:ℕ}{frame:Frame G df}(section_:SectionData frame)(group:Hol G)(ticket:TicketP R.alloy R.kit D Q)
    (budget:2 ≤ C){b K:ℕ}(floor:m ≤ b)(older:b ≤ j+1)(finer:j+1+1 ≤ K)(admitted:K ≤ N)
    (n cost P f d:ℕ)(np:0<n)(load_ok:∀t:(marks).Mode,t.val.card ≤ n)
    (tariff:fee charges s ≤ f)(grade:(rank) ≤ d)(period:R.family.S.a b/R.family.S.a K ≤ (R.family.path.levels.clock.hatBeta b)^cost)
    (cash:work n P f d+1+(WD f).pole+1 ≤ q)(support:(R.family.path.levels.budget (j+1)).supportExponent=100)
    {η:ℝ}(ep:0<η)
    (when_:WilsonOriginalOneArmOpticalDates.At R simple s n cost P f d (2*s.val.card+(a+∑v∈s.val,charges v))
      level C η budget np load_ok ep b (j+1) N per)
    {qc:ℕ}(deep:2*(qc+1)+8 ≤ upper.order)(age:qc+4 ≤ 3*k+2)
    (hard:6*upper.seats ≤ R.alloy.B.a.clock.J (j+1))
    (one:ready 1 ≤ j+1)(more:ready (high).op.count ≤ j+1)
    (previous:WilsonFirstReceivedEarnedFee.opening R simple (high).op.count qc upper.order k deep age
      (by norm_num:0<(1:ℝ)) ≤ j+1):
    Owned (N:=N) R simple hk D Q π Γ Ψ books ahead rows (j+1) b s P η:=by
  cases up
  cases down
  have rent:(1:ℝ)*(Coat.gStep (R.family.path.rep N per (j+1+1)).beta)^qc ≤ 1:=by
    rw [one_mul]
    exact pow_le_one₀ when_.positive.le when_.tilt
  have charge:Sale R simple hk D Q π Γ Ψ books base ahead rows upper lower b s P η:=by
    exact .filed course live way pass month hospital warm nn nn' calendar seen atStation section_ group ticket
      when_.mature budget le_rfl floor older finer admitted n cost f d (load_ok s) tariff grade period
      when_.begin_at cash rfl when_.jets support (work n P f d+2) (by norm_num:0<(1:ℝ)) le_rfl
      when_.failed_age when_.failed when_.fixed calendar.narrow calendar.load one more when_.wide when_.neighbor qc
      hard deep age (by norm_num:0<(1:ℝ)) rent previous np load_ok 1 ((cost:ℝ)/Real.log 3) ep
      (div_nonneg (Nat.cast_nonneg _) (Real.log_pos (by norm_num:1<(3:ℝ))).le) when_.optical
  exact ⟨j,rfl,base,S,S',a,a',upper,lower,charge⟩

end YM.Integration.WilsonOriginalOneArmBoardPair
end
