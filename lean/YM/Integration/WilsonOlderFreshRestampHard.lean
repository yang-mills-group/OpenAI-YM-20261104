import YM.Integration.WilsonOlderSignedOneMarkBooked
import YM.Integration.WilsonOlderFreshFiledStep

/-! The old hard owners paying the sign of the measured restamp and the unchanged student share the booked one-root bound. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshRestampHard
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


include cut course in
theorem weighted (simple : G.Simple) (late : WilsonReceivedSourceGross.opening R simple ≤ i)
    (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (shelved : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2)
    (s : (Stock.census V).Mode) (Z : Support (R.family.side i per)) (q : ℕ) (H : ℝ)
    (scope : ((Ψ i).p.supportExponent+2)*coverNumber (Ψ i).p.B Z≤H) {ε η δ : ℝ} (ep : 0<ε)
    (scheduled : WilsonOlderSignedOneMarkBooked.opening R simple (order+shelf+2) q H ep ≤ i)
    (unit : η≤1) (price : 0≤δ) (small : δ≤1) (cool : gf≤1) (holder : 0≤u) (kid : 0≤κ) :
    let change:=δ*gf^((order:ℝ)+1-η)*P.cost
    let toll:=Poly.toll P.w s
    let allCap:=(Spill.allOver (Ψ i).p)^(order+shelf+1)
    toll*(WilsonOlderSignedOneMarkMasks.fare (Ψ i).p Z u toll gross κ+
      WilsonOlderSignedOneMarkMasks.fare (Ψ i).p Z u toll (allCap*change) κ) ≤
        2*ε*(regulatorRun R.family N per m)^q := by
  intro change toll allCap
  have wt : 0≤toll:=(Poly.worth P.issued.earning.positive s).le
  have positive : 0<gf:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  have order_nonnegative : 0≤(order:ℝ):= by positivity
  have coeff : gf^((order:ℝ)+1-η)≤1:=Real.rpow_le_one positive.le cool (by linarith only [unit,order_nonnegative])
  have currency : P.cost≤1:=P.affordable.trans (inv_le_one_of_one_le₀ P.issued.Waffle.cool)
  have good : change≤Ω:=calc
    _ ≤ δ*gf^((order:ℝ)+1-η)*1:=mul_le_mul_of_nonneg_left currency (by positivity)
    _ ≤ δ:=by simpa only [mul_one] using mul_le_mul_of_nonneg_left coeff price
    _ ≤ 1:=small
    _ ≤ Ω:=P.issued.Waffle.cool
  have cap : 0≤allCap:=pow_nonneg (zero_le_one.trans (Spill.allOver_ge (Ψ i).p)) _
  have hard : 0≤hitWidth (Ψ i).p*u:=mul_nonneg (by unfold hitWidth; positivity) holder
  have sh : WilsonOlderSignedOneMarkMasks.fare (Ψ i).p Z u toll (allCap*change) κ ≤
      WilsonOlderSignedOneMarkMasks.fare (Ψ i).p Z u toll gross κ := by
    unfold WilsonOlderSignedOneMarkMasks.fare
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left good cap) (inv_nonneg.mpr wt)) (Real.exp_pos _).le) hard) kid
  have invoice:=WilsonOlderSignedOneMarkBooked.weighted R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades order
    shelf seats physical P simple late pass hospital shelved load s Z q H scope ep scheduled
  have extra:=(mul_le_mul_of_nonneg_left sh wt).trans invoice
  linarith only [invoice,extra, mul_add toll (WilsonOlderSignedOneMarkMasks.fare (Ψ i).p Z u toll gross κ)
    (WilsonOlderSignedOneMarkMasks.fare (Ψ i).p Z u toll (allCap*change) κ)]

end YM.Integration.WilsonOlderFreshRestampHard
