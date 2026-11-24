import YM.Integration.WilsonOlderSignedOneMarkRate
import YM.RG01.Slack

/-! The actual all-group word salary and its original marker radius in the
divided mask bill. The onset is independent of both physical regulators. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderSignedOneMarkBooked
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums
open Pert.Asymptotics

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)


local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "gf" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "u" => R.alloy.B.a.clock.forcedAllowance i
local notation "α" => (Ψ i).p.supportExponent+2
local notation "gross" => (Spill.allOver (Ψ i).p)^(order+shelf+1)*Ω

def opening {G : Gauge} (R : Run G) (simple : G.Simple) (n q : ℕ) (H : ℝ) {ε : ℝ} (ep : 0<ε) : ℕ :=
  (eventually_atTop.mp ((RG01.Physical.nextHat simple R.family.path.levels).and
    (WilsonOlderSignedOneMarkRate.paid R simple n q (C:=Real.exp H*8^n) (by positivity) ep))).choose

include cut course in
theorem weighted (simple : G.Simple) (late : WilsonReceivedSourceGross.opening R simple ≤ i)
    (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (shelved : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2)
    (s : (Stock.census V).Mode) (Z : Support (R.family.side i per)) (q : ℕ) (H : ℝ)
    (scope : ((Ψ i).p.supportExponent+2)*coverNumber (Ψ i).p.B Z≤H) {ε : ℝ} (ep : 0<ε)
    (scheduled : opening R simple (order+shelf+2) q H ep ≤ i) :
    Poly.toll P.w s * WilsonOlderSignedOneMarkMasks.fare (Ψ i).p Z u (Poly.toll P.w s) gross κ
      ≤ ε*(regulatorRun R.family N per m)^q := by
  let n:=order+shelf+2
  let A:=R.family.path.levels
  let x:=A.clock.hatBeta i
  let y:=A.clock.hatBeta (i+1)
  let β:=(R.family.path.rep N per (i+1)).beta
  have terms:=(eventually_atTop.mp ((RG01.Physical.nextHat simple A).and
    (WilsonOlderSignedOneMarkRate.paid R simple n q (C:=Real.exp H*8^n) (by positivity) ep))).choose_spec i scheduled
  have hp:0<β:=Overlay.beta_positive R.makes.wilson cut
  have band:β≤2*y:=(R.makes.wilson.represents N per (i+1) cut).band.2
  have bound : β≤4*x := band.trans (by linarith only [terms.1])
  let c:=Real.exp (((Ψ i).p.supportExponent+2)*coverNumber (Ψ i).p.B Z)
  have budget:=(WilsonReceivedSourceGross.original R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades
    order shelf seats physical P simple late pass hospital shelved load).2
  have price : gross≤ 8^n*x^n := calc
    _ ≤ (2:ℝ)^n/((Real.sqrt β)⁻¹)^(2*n) := budget
    _ = 2^n*β^n := by rw [div_eq_mul_inv,inv_pow,inv_inv,pow_mul,Real.sq_sqrt hp.le]
    _ ≤ 2^n*(4*x)^n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.le bound _) (by positivity)
    _ = 8^n*x^n := by rw [mul_pow,←mul_assoc,←mul_pow];norm_num
  have bill:c*gross≤(Real.exp H*8^n)*x^n := by
    rw [mul_assoc]
    exact mul_le_mul (Real.exp_monotone scope) price
      (mul_nonneg (pow_nonneg (zero_le_one.trans (Spill.allOver_ge _)) _) P.issued.Waffle.paysAbove.le)
      (Real.exp_pos _).le
  have keep:=terms.2 N per cut.le m hi (c*gross) (mul_nonneg (Real.exp_pos _).le
    (mul_nonneg (pow_nonneg (zero_le_one.trans (Spill.allOver_ge _)) _) P.issued.Waffle.paysAbove.le)) bill
  have hpnt:=(course.1.walk i hi cut.le).truep.point
  have h₀ : hitWidth (Ψ i).p=hitWidth (A.budget i):=congrArg hitWidth hpnt
  have wt : 0<Poly.toll P.w s:=Poly.worth P.issued.earning.positive s
  change Poly.toll P.w s*((hitWidth (Ψ i).p*u)*(c*((Poly.toll P.w s)⁻¹*gross))/κ) ≤ _
  calc
    _ = (hitWidth (A.budget i)*u)*(c*gross)/κ := by rw [h₀];field_simp
    _ ≤ _ := keep

end YM.Integration.WilsonOlderSignedOneMarkBooked
