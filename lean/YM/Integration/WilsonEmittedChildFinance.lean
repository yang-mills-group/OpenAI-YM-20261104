import YM.Integration.WilsonEmittedLandedGraphField
import YM.Integration.WilsonMeasuredSemesterSubpower
import YM.Integration.WilsonOlderFreshGraphHostTarget

/-! The original lower post pays its singleton tariff uniformly in its radius change. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedChildFinance
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

theorem price (H:upperPost) (L:lowerPost) {w:ℝ} (hw:0<w)
    (earned:∃h C:ℝ,1≤h ∧ C≤budgetR R (j+1) ∧ (∀v,L.w v=w/((Oak.expenseReal R hk D Q π Γ books upper H.op H.lesson ahead school.order school.horizon)^6*h)) ∧ L.cost=h⁻¹*C) :
    (Poly.toll L.w u)⁻¹ * L.cost ≤ w⁻¹*(Oak.expenseReal R hk D Q π Γ books upper H.op H.lesson ahead school.order school.horizon)^6*budgetR R (j+1) := by
  obtain ⟨h,C,hh,cap,rad,fee⟩:=earned
  have h0:0<h:=zero_lt_one.trans_le hh
  have one: Poly.toll L.w u=L.w ():=by simp [Poly.toll,Census.fire]
  rw [one,rad,fee]
  calc
    _ = w⁻¹*(Oak.expenseReal R hk D Q π Γ books upper H.op H.lesson ahead school.order school.horizon)^6*C:=by simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]; field_simp
    _ ≤ _:=mul_le_mul_of_nonneg_left cap (mul_nonneg (inv_nonneg.mpr hw.le) (Even.pow_nonneg (by decide:Even 6) _))

def onset := max (WilsonMeasuredSemesterSubpower.onset R 6 zero_lt_one)
  (WilsonMeasuredSemesterSubpower.onset R 1 zero_lt_one)

include course cut pass in
theorem original (H:upperPost) (L:lowerPost) (live:onset R ≤ j+1) (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (shelved:school.horizon≤R.alloy.B.a.clock.J (j+1)) (load:school.pieces≤Burn.horizon k+2)
    {w M:ℝ} (hw:0<w)(mass:0≤M)(amp:w⁻¹ ≤ 2*H₂*M)
    (earned:∃h C:ℝ,1≤h ∧ C≤budgetR R (j+1) ∧ (∀v,L.w v=w/((Oak.expenseReal R hk D Q π Γ books upper H.op H.lesson ahead school.order school.horizon)^6*h)) ∧ L.cost=h⁻¹*C) :
    (Poly.toll L.w u)⁻¹ * L.cost ≤ 2*H₂^3*M := by
  have funded:=WilsonMeasuredSemesterSubpower.charged R hk D Q π Γ Ψ course books upper cut ahead
    actors pieces grades school.order school.horizon school.pieces (head) H 6 zero_lt_one
    ((le_max_left _ _).trans live) pass hospital shelved (H.capacity.trans_le load)
  rw [Real.rpow_one] at funded
  have birth:1≤H₂:=(R.alloy.B.a.fits.delayed _).le
  have z0:0≤budgetR R (j+1):=zero_le_one.trans (budget_pos (R:=R) (i:=j+1))
  have cap:= (eventually_atTop.mp (WilsonMeasuredSemesterSubpower.budget R 1 zero_lt_one)).choose_spec (j+1)
    ((le_max_right _ _).trans live) (budgetR R (j+1)) z0 (min_le_right ..)
  rw [Real.rpow_one,pow_one] at cap
  have fee:=price R hk D Q π Γ Ψ books ahead school floor actors model H L hw earned
  apply fee.trans
  calc
    _ ≤ ((2*H₂*M)*H₂)*H₂:=mul_le_mul (mul_le_mul amp funded (by positivity) (by positivity)) cap z0 (by positivity)
    _ = _ := by ring

end YM.Integration.WilsonEmittedChildFinance
end
