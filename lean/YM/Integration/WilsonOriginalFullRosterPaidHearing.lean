import YM.Integration.WilsonOriginalFullRosterEarnedBill
import YM.Integration.WilsonOriginalFullRosterCouplingClock
import YM.Integration.WilsonOriginalMountedFailedHalo

/-! The original ordinary Wilson edge at coupling precision on its true older clear receiver. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFullRosterPaidHearing
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
theorem original {s:(marks).Mode}{charges:V→ℕ}{q h target:ℕ}{ε δ C:ℝ}
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(live:j+1 < N)
    (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)(nn:∀v,0 ≤ S v)(nn':∀v,0 ≤ S' v)
    (read:WilsonOriginalDatedCensusEdge.Reading R simple hk D Q π Γ Ψ books base ahead
      (rows (j+1+1)) (rows (j+1)) upper lower s charges q h target ε δ C)
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
    (U:Config G (R.family.side b per))
    (tilt:(Real.exp (WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op b per)
      (R.family.path.β N per (b+1)) U))^2 ≤ 2)
    (earned:WilsonOriginalFullRosterFiledHearing.Earned R simple hk D Q π Γ Ψ books base ahead rows upper lower
      course live way pass month hospital read p tol older U):
    (carried).hard=(high).output.hard ∧ ((upper.appointment.row upper.x).A.density (upper.appointment.row upper.x).x=
      LocalComparison.actualPush R.family N per (j+1) (rows (j+1+1))) ∧
    ‖WilsonOriginalJointTrialHearing.fee R N per U rows (j+1) s-
      WilsonOriginalOccupiedWindow.credit R (marks) (N:=N) older Ψ (upper.appointment.row upper.x) s U‖ ≤
      WilsonOriginalOrdinaryFaceOrder.constant s s.val.card*(gAt b)^P:=by
  have inc:0 ≤ C:=zero_le_two.trans budget
  obtain ⟨gp,cold,hp,hs,fp,fs,wallet,raw,wage,old,peg⟩:=(eventually_atTop.mp
    (WilsonOriginalFullRosterCouplingClock.original R simple n cost P f d C inc)).choose_spec b start older finer admitted period (per:=per)
  have finePow:0 ≤ (gAt (j+1+1))^q:=pow_nonneg fp.le _
  have enough:1 ≤ q:=by omega
  obtain ⟨q₀,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega:q≠0)
  have cooled:(1+ε)*(gAt (j+1+1))^(q₀+1) ≤ 1:=(mul_le_mul_of_nonneg_right (by linarith only [eps] : 1+ε ≤ 1+1) finePow).trans
    (WilsonOriginalCensusChronologicalMoney.cooled fp.le fs q₀)
  obtain ⟨hard,joint,F,width,cut,accuracy,realW,realRaw,realM,rent,heard⟩:=
    WilsonOriginalFullRosterEarnedBill.original R simple hk D Q π Γ Ψ books base ahead rows upper lower
      course live way pass month hospital warm nn nn' read budget (by linarith only [hs]) cooled p tol older U earned
  refine ⟨hard,joint,heard.trans ?_⟩
  have hz:1 ≤ H:=(R.family.path.levels.fits.delayed (j+1)).le
  have small:gAt b ≤ 1:=by linarith only [gp,cold]
  have z:1 ≤ (gAt (j+1))⁻¹:=(one_le_inv₀ hp).mpr (by linarith only [hs])
  have ww:=pow_le_pow_right₀ hz tariff
  have zz:=pow_le_pow_right₀ z grade
  have W:=realW.trans ((mul_le_mul_of_nonneg_left ww inc).trans wallet)
  have rawSize:=realRaw.trans ((mul_le_mul_of_nonneg_left zz (mul_nonneg inc (pow_nonneg (zero_le_one.trans hz) _))).trans raw)
  have oldM:=mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (Nat.add_le_add_right tariff 2)) inc) zz
    (pow_nonneg (zero_le_one.trans z) _) (mul_nonneg inc (pow_nonneg (zero_le_one.trans hz) _))
  have olderRent:=rent.trans ((mul_le_mul (by linarith only [eps,budget] : 1+ε ≤ C)
    (pow_le_pow_of_le_one fp.le (by linarith only [fs]) prior) finePow inc).trans old)
  have actual:(vac).p=R.family.path.levels.budget (j+1):=(course.1.walk (j+1) (Nat.le_succ_of_le base) live.le).truep.point
  have alpha:1 ≤ F.α:=by rw [width,actual,support];norm_num
  have light:=WilsonOriginalMountedRegularFare.small (work n P f d) (WD f).pole (RD d).pole F.h gp cold alpha
    ((cut.trans shape).symm.le) W rawSize F.rent_nn F.gross_nn olderRent ((accuracy.trans_le jets).trans peg)
  have seats:P+(DD f d).pole*s.val.card ≤ work n P f d:=Nat.add_le_add_left (Nat.mul_le_mul_left _ count) _
  let cap:ℝ:=(work n P f d+1+(WD f).pole+(RD d).pole:ℕ)
  have cap₀:0 ≤ cap:=Nat.cast_nonneg _
  have fit:F.h ≤ Nat.ceil (cap*(1+Real.log (gAt b)⁻¹)):=by
    rw [cut,shape]
    exact Nat.ceil_mono (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) cap₀)
  have failed:=WilsonOriginalMountedFailedHalo.atSpring R simple n cap₀ tp.le course floor older live F support.le
    count fit P (DD f d).pole p ((Nat.add_le_add_right seats 2).trans reserve) U aged tilt
  exact WilsonOriginalMountedOrder.original F b p (DD f d).pole P tp.le (zero_le_one.trans hz) gp small
    ((realM.trans oldM).trans wage) (light.trans (pow_le_pow_of_le_one gp.le small seats)) failed

end YM.Integration.WilsonOriginalFullRosterPaidHearing
end
