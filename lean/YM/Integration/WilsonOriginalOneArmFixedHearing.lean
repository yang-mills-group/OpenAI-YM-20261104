import YM.Integration.WilsonReceivedChronologicalTwoFlatSale
import YM.Integration.WilsonOriginalOneArmHearingRate
import YM.Integration.WilsonOriginalSubmittedWholeSpring
import YM.Integration.WilsonOriginalCensusFiledPhysicalEdge

/-! The native dual-flat sale keeps the two actual independently issued deposits, their captured hard and the prior. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalOneArmFixedHearing
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
open WilsonOriginalOccupiedCorridor

local notation "ready" l:max => WilsonMeasuredSemesterSubpower.onset R l (by norm_num : 0<(1:ℝ))
local notation "gAt" i:max => regulatorRun R.family N per i
open WilsonReceivedChronologicalTwoFlatSale (Sale)
open private total from YM.Integration.WilsonOriginalCensusFiledPhysicalEdge
open private relative from YM.Integration.WilsonMeasuredImpulseCalendar

/-- Reopen a paid two-flat sale at a true clear board on the same report.
Its real stage and optical tariff pay the signed hard part directly at W. -/
theorem original {u b:ℕ}{s:(marks).Mode}{P size:ℕ}{η:ℝ}
    (bought:Sale R simple hk D Q π Γ Ψ books base ahead rows upper lower u b s P size η)
    (W:Config G (R.family.side b per))(clear:flags (R.family.path.rep N per b).p.threshold W=∅)
    (tilt:(Real.exp (WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op b per)
      (R.family.path.β N per (b+1)) W))^2≤2):
    ‖WilsonOriginalJointTrialHearing.fee R N per W rows (j+1) s‖≤
      (WilsonOriginalOrdinaryFaceOrder.constant s s.val.card+η*2^P*((shards (marks) s).card:ℝ))*(gAt b)^P:=by
  cases bought with
  | @issued charges q h target ε δ C course live way pass month hospital warm nn nn' calendar seen budget eps K floor older finer admitted n cost f d count tariff grade period start prior shape jets support p tol tp reserve aged atStation df frame section_ group ticket mature failure past mu ub fixed narrow load one more wide neighbor capture qc hardFloor hardDeep hardAge err ep rented opened np stage load_ok cap Z center atHome resident drift E ep₀ E0 enclosed reg room late span =>
    have actual:(Ψ b).p=(R.family.path.rep N per b).p:=(course.1.walk b floor (older.trans live.le)).truep.point.trans (R.makes.wilson.represents N per b (older.trans live.le)).vac.symm
    have healthy:flags (Ψ b).p.threshold W=∅:=by rw [actual];exact clear
    have soft:=WilsonOriginalFullRosterPricedFaces.original (h:=h) R simple hk D Q π Γ Ψ books base ahead rows upper lower
      course live way pass month hospital warm nn nn' calendar seen atStation section_ group ticket mature
      budget eps floor older finer admitted n cost P f d count tariff grade period start prior shape jets support
      p tp reserve aged W tilt failure (fixed.trans ub) healthy
    have enough (t:(marks).Mode):(∑v∈t.val,upper.grades v)+1≤(∑v:V,upper.grades v)+1:=
      Nat.succ_le_succ (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>Nat.zero_le _))
    have hard:=WilsonOriginalOneArmHearingRate.original R hk D Q π Γ Ψ books (Nat.le_succ_of_le base) live ahead upper
      simple way course pass hospital narrow load one more wide neighbor ticket floor older (Nat.zero_lt_succ j)
      _ qc enough hardFloor hardDeep hardAge ep rented opened s charges nn calendar.high_wage
      n drift P np load_ok E η E0 ep₀ stage late span W healthy
    exact total soft.2.2 hard (relative R.makes simple N per b (j+1) older live.le)
      (ActualRunKernelPackets.regulator_pos R N per (j+1) live.le).le ep₀.le (Nat.cast_nonneg _)

end YM.Integration.WilsonOriginalOneArmFixedHearing
end
