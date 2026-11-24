import YM.Integration.WilsonCapturedNativeStampCharge
import YM.Integration.WilsonCapturedStampSourceLimit
import YM.Integration.WilsonCapturedSoldReportingStrip
import YM.Integration.WilsonOriginalRestampedSourceIncome

/-! Both reporting debits on the identical coissued lower pupil, using only its native
Recharged income and Waffle figure. The onset precedes both regulators and every held test. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedSoldClockIncome
open Function Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler AllOrder.Transit.WheelP
open QuadraticLocal.Rebirth QuadraticLocal.Affinity WilsonOriginalReceivedChain Stationary Multi
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open AnalyticBridge VerifiedReset RemainderComparison
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {m N per k i : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (hi : m ≤ i)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i hi physical)

local notation "stud" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors P.model order P.voter
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "op" => R.family.path.levels.clock.op i per
local notation "stipend" => (fig).produce (op).ratio.count*P.cost
local notation "markUp" => Oak.rebate R hk D Q π Γ hi P.op P.lesson
local notation "rooted" => Mutation.stamp stud (Γ i) (Oak.grade0 R hk D Q π Γ hi P.lesson)
  (Burn.horizon k+2) order




open Filter WilsonCapturedClockRankProjection WilsonCapturedStampSourceLimit
open scoped Topology
local notation "liveClock" => (caliber (Γ i) (Oak.grade0 R hk D Q π Γ hi P.lesson)).back (Burn.horizon k+2)
local notation "coinHat" => R.alloy.B.a.clock.hatBeta i

def Allowed (s k i:ℕ):Prop:=
  0 < i ∧ k ≤ R.alloy.B.a.clock.J i ∧ Real.exp 1 ≤ R.alloy.B.a.clock.hatBeta i ∧
    budgetR R i ≤ 2*R.alloy.B.a.clock.hatBeta i ∧ 4096*cap G s ≤ R.alloy.B.a.clock.hatBeta i

theorem calendar (simple:G.Simple)(s k:ℕ):∀ᶠi:ℕ in atTop,Allowed R s k i:=by
  have clocks:=Next.Rank.Station.hat_rate R.family.path.levels simple
  filter_upwards [eventually_ge_atTop 1,R.alloy.B.a.fits.deep.eventually_ge_atTop k,
    clocks.eventually_ge_atTop (Real.exp 1),RG01.Physical.nextHat simple R.alloy.B.a,
    clocks.eventually_ge_atTop (4096*cap G s)] with i opened listed hot stride salary
  have positive:1 ≤ R.alloy.B.a.clock.hatBeta (i+1):=(R.alloy.B.a.fits.delayed _).le
  have upper:budgetR R i ≤ R.alloy.B.a.clock.hatBeta (i+1):=
    (min_le_right _ _).trans ((Real.rpow_le_rpow_of_exponent_le positive
      (show Beaming.grain (R.alloy.B.a.clock.J i) ≤ 1 by unfold Beaming.grain;apply (div_le_one (by positivity)).2;simp)).trans_eq (Real.rpow_one _))
  exact ⟨opened,listed,hot,upper.trans stride,salary⟩

theorem original (simple:G.Simple)(gr:WilsonPhysicalHistoryPriorAperture.Paid R.rolls D φ R.alloy.delay)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(cut:i < N)(pass:Pass D Q R.alloy R.kit)
    (month:Scholar.Month R.rolls D Q R.alloy.delay)(fits:order ≤ Burn.horizon k+1)
    (narrow:shelf ≤ R.alloy.B.a.clock.J i){s:ℕ}(date:Allowed R s k i)(usable:0 < shelf):
    Scene.Armada (rooted) P.w grades σ ((markUp)*(stipend)) order P.op.count shelf ∧
    0 < σ ∧ σ⁻¹ ≤ Real.sqrt (Real.log (coinHat)) ∧
    ∀(pole q r:ℕ),pole ≤ shelf+1 → q ≤ order → q ≤ s →
      charge (liveClock) (-(pole:ℤ)) q r (fun v=>WilsonCapturedCoveredSourceWage.fare G v r σ ((markUp)*(stipend))) ≤
        (coinHat)^6:=by
  obtain ⟨opened,listed,hot,growth,tariff⟩:=date
  obtain ⟨actual,_,pc,bill⟩:=WilsonOriginalRestampedSourceIncome.original R hk D Q π Γ Ψ books ahead actors
    pieces grades order shelf seats hi physical P course cut pass month fits narrow
  obtain ⟨sp,rootStrip,small,ramp⟩:=WilsonCapturedSoldReportingStrip.original R hk D Q π Γ Ψ books ahead
    actors pieces grades order shelf seats hi physical P simple gr listed opened hot
  obtain ⟨credit,honest⟩:=WilsonOriginalMeasuredReentry.credited R hk D Q pass π Γ Ψ course
    hi cut P.lesson books P.op ahead month order shelf fits narrow
  have payroll:1 ≤ ((order+1:ℕ):ℝ):=by exact_mod_cast Nat.succ_pos order
  have tuition:=(le_mul_of_one_le_left (zero_le_one.trans credit.quota) payroll).trans
    (credit.attendance.trans honest)
  have b:0 ≤ budgetR R i:=pc.trans bill
  have hH:0 ≤ (coinHat):=(Real.exp_pos _).le.trans hot
  refine ⟨actual,sp,rootStrip,?_⟩
  intro pole q r marked held stage
  let f(v:ℕ):=WilsonCapturedCoveredSourceWage.fare G v r σ ((markUp)*(stipend))
  have smallSum:=WilsonCapturedStampSourceLimit.paid G stage r sp pc bill small ramp
  have pp:0 ≤ 256*(budgetR R i)^3*(coinHat)*cap G s:=by have w:=WilsonCapturedStampSourceLimit.positive G s;positivity
  calc
    _ ≤ _:=WilsonCapturedNativeStampCharge.filed G (Γ i) (Oak.grade0 R hk D Q π Γ hi P.lesson)
      credit pole q r marked usable held sp pc
    _ ≤ (budgetR R i)*(256*(budgetR R i)^3*(coinHat)*cap G s):=by
      apply (mul_le_mul_of_nonneg_left smallSum (zero_le_one.trans credit.quota)).trans
      exact mul_le_mul_of_nonneg_right tuition pp
    _=256*(budgetR R i)^4*(coinHat)*cap G s:=by ring
    _ ≤ 256*(2*(coinHat))^4*(coinHat)*cap G s:=by
      have c:=WilsonCapturedStampSourceLimit.positive G s;gcongr
    _=(4096*cap G s)*(coinHat)^5:=by ring
    _ ≤ (coinHat)*(coinHat)^5:=mul_le_mul_of_nonneg_right tariff (by positivity)
    _=_:=by ring

end YM.Integration.WilsonCapturedSoldClockIncome
