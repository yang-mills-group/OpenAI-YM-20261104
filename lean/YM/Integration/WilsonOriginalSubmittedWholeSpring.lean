import YM.Integration.WilsonOriginalFullRosterPricedFaces
import YM.Integration.WilsonOriginalCensusFiledClearHearing
import YM.Integration.WilsonOriginalCensusFiledPhysicalEdge
import YM.Integration.WilsonMeasuredImpulseCalendar

/-! The signed whole ordinary numerical return on an arbitrary earlier clear board.
The same upper Filed pays the compatible occupied credit against the same posterior. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSubmittedWholeSpring
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
variable (upper:WilsonOriginalDatedCensusInput.Filed (i:=j+1) (N:=N) R hk D Q π Γ Ψ books (Nat.le_succ_of_le base) ahead S a (rows (j+1+1)))
  (lower:WilsonOriginalDatedCensusInput.Filed (i:=j) (N:=N) R hk D Q π Γ Ψ books base ahead S' a' (rows (j+1)))
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
theorem original {s:(marks).Mode}{charges:V→ℕ}{q h target:ℕ}{ε δ C:ℝ}
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(live:j+1 < N)
    (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)(nn:∀v,0 ≤ S v)(nn':∀v,0 ≤ S' v)
    (calendar:WilsonOriginalSparseCensusEdge.Calendar R simple hk D Q π Γ Ψ books base ahead
      (rows (j+1+1)) (rows (j+1)) upper lower charges q ε δ C)
    (seen:∀t:Hot (marks),t.val.val⊆s.val → WilsonOriginalSparseCensusEdge.Face R hk D Q π Γ Ψ books
      base ahead (rows (j+1+1)) (rows (j+1)) upper lower t (calendar.front t) charges calendar.tube target δ)
    (atStation:WilsonOriginalFullRosterDatedReturn.station R simple
      (WilsonOriginalFullRosterBookedHearing.roof upper.grades lower.grades charges target) (Fintype.card V) ≤ j)
    {df:ℕ}{frame:Frame G df}(section_:SectionData frame)(group:Hol G)(ticket:TicketP R.alloy R.kit D Q)
    (mature:WilsonCenteredCaptureClock.first R simple ≤ j+1)
    (budget:2 ≤ C)(eps:ε ≤ 1){b K:ℕ}(floor:m ≤ b)(older:b ≤ j+1)(finer:j+1+1 ≤ K)(admitted:K ≤ N)
    (n cost P f d:ℕ)(count:s.val.card ≤ n)(tariff:fee charges s ≤ f)(grade:(rank) ≤ d)
    (period:R.family.S.a b/R.family.S.a K ≤ (R.family.path.levels.clock.hatBeta b)^cost)
    (start:(eventually_atTop.mp (WilsonOriginalFullRosterCouplingClock.original R simple n cost P f d C
      (zero_le_two.trans budget))).choose ≤ b)
    (prior:work n P f d+1+(WD f).pole+1 ≤ q)
    (shape:h=WilsonOriginalMountedRegularFare.crop (work n P f d+1+(WD f).pole+(RD d).pole) (gAt b))
    (jets:δ ≤ C*(gAt (j+1+1))^(work n P f d+1+1))
    (support:(R.family.path.levels.budget (j+1)).supportExponent=100)
    (p:ℕ){tol:ℝ}(tp:0 < tol)(reserve:work n P f d+2 ≤ p)
    (aged:WilsonOriginalMountedFailedHalo.first R simple n
      (Nat.cast_nonneg (work n P f d+1+(WD f).pole+(RD d).pole)) tp.le ≤ b)
    (failure:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple p tp)).choose ≤ j+1)
    (fixed:WilsonSingleHardRadius.first R simple ≤ b)

    (narrow:upper.shelf ≤ R.alloy.B.a.clock.J (j+1))(load:(high).op.count ≤ Burn.horizon k+2)
    (one:ready 1 ≤ j+1)(more:ready (high).op.count ≤ j+1)
    (wide:(eventually_atTop.mp ((RG01.Physical.hats simple R.alloy.B.a).eventually_ge_atTop 20)).choose ≤ j+1)
    (neighbor:(eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ j+1)
    (qc:ℕ)
    (hardFloor:6*upper.seats ≤ R.alloy.B.a.clock.J (j+1))(hardDeep:2*(qc+1)+8 ≤ upper.order)(hardAge:qc+4 ≤ 3*k+2)
    {err:ℝ}(ep:0<err)(rented:err*(Coat.gStep (R.family.path.rep N per (j+1+1)).beta)^qc ≤ 1)
    (opened:WilsonFirstReceivedEarnedFee.opening R simple (high).op.count qc upper.order k hardDeep hardAge ep ≤ j+1)

    (np:0 < n)(load_ok:∀t:(marks).Mode,t.val.card ≤ n)
    (drift:ℕ)(E η:ℝ)(ep₀:0 < η)(E0:0 ≤ E)
    (optical:WilsonOriginalCensusFiledClearHearing.Opening R simple n drift
      (2*s.val.card+(a+∑v∈s.val,charges v)) P np load_ok E η E0 ep₀ b (j+1))
    (W:Config G (R.family.side b per))(clear:flags (Ψ b).p.threshold W=∅)
    (tilt:(Real.exp (WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op b per)
      (R.family.path.β N per (b+1)) W))^2 ≤ 2):
    ‖WilsonOriginalJointTrialHearing.fee R N per W rows (j+1) s‖ ≤
      (WilsonOriginalOrdinaryFaceOrder.constant s s.val.card+η*2^P*((shards (marks) s).card:ℝ))*(gAt b)^P:=by
  have soft:=WilsonOriginalFullRosterPricedFaces.original (h:=h) R simple hk D Q π Γ Ψ books base ahead rows upper lower
    course live way pass month hospital warm nn nn' calendar seen atStation section_ group ticket mature
    budget eps floor older finer admitted n cost P f d count tariff grade period start prior shape jets support
    p tp reserve aged W tilt failure fixed clear
  have enough (t:(marks).Mode):(∑v∈t.val,upper.grades v)+1≤(∑v:V,upper.grades v)+1:=
    Nat.succ_le_succ (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>Nat.zero_le _))
  have hard:=WilsonOriginalCensusFiledClearHearing.original R hk D Q π Γ Ψ books (Nat.le_succ_of_le base) live ahead upper
    simple way course pass hospital narrow load one more wide neighbor ticket floor older (Nat.zero_lt_succ j)
    _ qc enough hardFloor hardDeep hardAge ep rented opened s charges nn calendar.high_wage
    n drift P np load_ok E η E0 ep₀ optical W clear
  exact total soft.2.2 hard (relative R.makes simple N per b (j+1) older live.le)
    (ActualRunKernelPackets.regulator_pos R N per (j+1) live.le).le ep₀.le (Nat.cast_nonneg _)

end YM.Integration.WilsonOriginalSubmittedWholeSpring
end
