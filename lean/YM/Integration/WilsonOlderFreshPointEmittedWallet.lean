import YM.Integration.WilsonEmittedChildFinance
import YM.Integration.WilsonEmittedPointChildCash
/-! The actual graduated lower row of a specified geometric child.
Its full film can be restored in the parent norm before summing stages. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointEmittedWallet
open Push.AbsoluteSums Next.Foundations
open Filter Labels Source Planned.GuardedAtom Push.Local
open WilsonOriginalReceivedChain
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Stationary Comparison.RG02 Comparison.RG02.Order Further.PhysicalPeriodLimitF933 Laurent
open RG16 Pert.Asymptotics WilsonMeasuredRankedResidual
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {m j N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  (school : Syl.School k) (floor : m ≤ j)
  (actors : Unit → Set ℂ) {inputRank : ℕ}
  {passport : Earn.Passport (R.family.side ((j+1)+1) per) Unit}
  {entries : Type} (model : entries → Row passport (Stock.census Unit) G (Wallet actors))
local notation "pieces" => (fun _ : Unit => (⊥ : Submodule ℝ ℂ))
local notation "grades" => (fun _ : Unit => inputRank)
local notation "upper" => (floor.trans (Nat.le_succ j))
local notation "rp" => Ψ (j+1)
local notation "bare" => Ψ ((j+1)+1)
local notation "head" => fun (x:Wallet actors) (U:Config G (R.family.side ((j+1)+1) per)) =>
  ((bare).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut model (Coat.gStep (bare).beta) x U)
local notation "earlier" => (fun x:Wallet actors => LocalComparison.actualPush R.family N per (j+1) (head x))
local notation "upperPost" => Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q π Γ Ψ books ahead
  actors pieces grades school.order school.horizon school.pieces (j+1) upper (head)
local notation "lowerPost" => Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q π Γ Ψ books ahead
  actors pieces grades school.order school.horizon school.pieces j floor earlier
local notation "g" => Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta
local notation "gm" => Pert.Asymptotics.regulatorRun R.family N per m
local notation "y" => (passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin ()
local notation "u" => (Stock.census Unit).fire ()
local notation "κ" => LocalComparison.forcedDivisor R.family (j+1)
variable (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (path:PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ) (cut:j+1<N)
    (pass:Pass D Q R.alloy R.kit) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (narrow:school.horizon≤R.alloy.B.a.clock.J (j+1))
local notation "H₂" => R.alloy.B.a.clock.hatBeta ((j+1)+1)

open OPE.Therm FormalBulk08 FormalBulk08.Roof
variable (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
def activation :=max (WilsonEmittedChildFinance.onset R) (max
  (eventually_atTop.mp (WilsonOlderFreshGraphSlowPreimages.block R simple slow inputRank (show 0<(1:ℝ) by norm_num))).choose
  (eventually_atTop.mp (RG01.Physical.nextHat simple R.family.path.levels)).choose)
include course cut pass in
theorem original (H:upperPost)(L:lowerPost)(live:activation (inputRank:=inputRank) R simple slow ≤ j+1)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (shelved:school.horizon≤R.alloy.B.a.clock.J (j+1))(load:school.pieces≤Burn.horizon k+2)
    {dmax:ℕ}(f:Dawn.Studio dmax)(pin:Site (R.family.S.block (j+1))) {w:ℝ}(hw:0<w)
    (amp:w⁻¹≤2*H₂*(1+‖Dawn.throughW pin dmax (Elm.growL R.family.path.levels (j+1)) f‖))
    (earned:∃h C:ℝ,1≤h ∧ C≤budgetR R (j+1) ∧
       (∀v,L.w v=w/((Oak.expenseReal R hk D Q π Γ books upper H.op H.lesson ahead school.order school.horizon)^6*h)) ∧ L.cost=h⁻¹*C):
    (((R.family.S.block (j+1)).val:ℝ)^inputRank)*((Poly.toll L.w u)⁻¹*L.cost) ≤
      32*(R.alloy.B.a.clock.hatBeta (j+1))^4*(1+‖f‖):=by
  have gates:=max_le_iff.mp live
  have windows:=max_le_iff.mp gates.2
  have repaid:=WilsonEmittedChildFinance.original (R:=R) (hk:=hk) (D:=D) (Q:=Q) (π:=π) (Γ:=Γ)
    (Ψ:=Ψ) (course:=course) (books:=books) (floor:=floor) (school:=school) (ahead:=ahead) (actors:=actors)
    (model:=model) (cut:=cut) (pass:=pass) H L gates.1 hospital shelved load hw
    (show 0≤1+‖Dawn.throughW pin dmax (Elm.growL R.family.path.levels (j+1)) f‖ by positivity) amp earned
  have film:=Dawn.through_le pin (Elm.growL R.family.path.levels (j+1)) f
  have β₀:0≤H₂:=(R.alloy.B.a.fits.delayed _).le.trans' zero_le_one
  have row: (Poly.toll L.w u)⁻¹*L.cost ≤ 2*H₂^3*(1+‖f‖):=
    repaid.trans (mul_le_mul_of_nonneg_left (add_le_add_right film 1) (by positivity))
  have side:((R.family.S.block (j+1)).val:ℝ)^inputRank≤H₂:=by
    have done:=(eventually_atTop.mp (WilsonOlderFreshGraphSlowPreimages.block R simple slow inputRank
      (show 0<(1:ℝ) by norm_num))).choose_spec (j+1) windows.1
    change ((R.family.path.levels.S.block (j+1)).val:ℝ)^inputRank ≤ H₂
    have levels:R.family.path.levels=R.alloy.B.a:=rfl
    rw [levels]
    simpa only [Real.rpow_one] using done
  have growth:H₂≤2*R.alloy.B.a.clock.hatBeta (j+1):=
    (eventually_atTop.mp (RG01.Physical.nextHat simple R.family.path.levels)).choose_spec (j+1) windows.2
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left row (by positivity)
    _ ≤ H₂*(2*H₂^3*(1+‖f‖)) := mul_le_mul_of_nonneg_right side (by positivity)
    _ = 2*H₂^4*(1+‖f‖):=by ring
    _ ≤ 2*(2*R.alloy.B.a.clock.hatBeta (j+1))^4*(1+‖f‖):=by gcongr
    _ = _:=by ring

end YM.Integration.WilsonOlderFreshPointEmittedWallet
end
