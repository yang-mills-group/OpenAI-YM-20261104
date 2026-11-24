import YM.Integration.WilsonReceivedCloseSignedPrice
import YM.Integration.WilsonReceivedCloseSourceCalendar
import YM.Integration.WilsonReceivedCloseOrdinaryScale

/-! A specified incoming post produces one filed lower Wilson post at each
enrolled close date. The quiet face of its genuine signed estimate pays that
post's regular error jointly with the inherited masks and marker radii. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseRetainedRent
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open scoped BigOperators

variable {G : Gauge} (R : Run G) {m b N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (mb : m ≤ b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census V))

local notation "read" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "P" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y

local notation "g" => regulatorRun R.family N per
def fee (p q:ℕ) : ℝ := (1+2*(3:ℝ)^p)*3^q
theorem nonneg (p q:ℕ) : 0 ≤ fee p q := by unfold fee; positivity

theorem scalar (p q:ℕ) (extra:q+2≤p) {x t α η:ℝ} (xp:0<x) (tp:0<t) (small:x≤1)
    (band : t⁻¹ ≤ 3*x⁻¹) (prior:α ≤ x^p) (gate:fee p q*x≤η) :
    x⁻¹ * (α+2*(3*x)^p) ≤ η*t^q := by
  have compare : x ≤ 3*t := calc
    x = (x*t)*t⁻¹ := by field_simp
    _ ≤ (x*t)*(3*x⁻¹) := mul_le_mul_of_nonneg_left band (mul_pos xp tp).le
    _ = 3*t := by field_simp
  have powers : x⁻¹*x^p ≤ x^q*x := calc
    _ ≤ x⁻¹*x^(q+2) := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one xp.le small extra) (inv_pos.mpr xp).le
    _ = x^q*x := by rw [pow_add]; field_simp
  calc
    _ ≤ x⁻¹*(x^p+2*(3*x)^p) := mul_le_mul_of_nonneg_left (by linarith only [prior]) (inv_pos.mpr xp).le
    _ = (1+2*(3:ℝ)^p)*(x⁻¹*x^p) := by rw [mul_pow]; ring
    _ ≤ (1+2*(3:ℝ)^p)*(x^q*x) := mul_le_mul_of_nonneg_left powers (by positivity)
    _ ≤ ((1+2*(3:ℝ)^p)*x)*(3*t)^q := by
      rw [show (1+2*(3:ℝ)^p)*(x^q*x)=((1+2*(3:ℝ)^p)*x)*x^q by ring]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ xp.le compare _) (by positivity)
    _ = (fee p q*x)*t^q := by rw [mul_pow]; unfold fee; ring
    _ ≤ η*t^q := mul_le_mul_of_nonneg_right gate (pow_nonneg tp.le _)

section Course
open Poly
variable (simple : G.Simple)
local notation "usual" p:max q:max ε:max pos:max => WilsonReceivedCloseSourceCalendar.reporter_fee
  (fee:=fee p q) (ε:=ε) R simple (nonneg p q) pos
local notation "signed" d:max a:max p:max cap:max hc:max => WilsonReceivedCloseSignedPrice.opening
  R simple d a p seats (cap:=cap) hc (η:=1) zero_lt_one (ε:=1) zero_le_one
local notation "next" => (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose
local notation "cool" => (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose

include mb in
theorem original (P₀ : P b mb source)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (path : PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ) (top : b < N)
    (pass : Pass D Q R.alloy R.kit) (scroll : VowsR.LawScroll G φ)
    (chamber : VowsR.Chamber scroll R.kit D Q books) (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J m)
    (load : seats ≤ Burn.horizon k+2) (packed : order+shelf ≤ Burn.horizon k+2)
    (p q : ℕ) (deep : 2*p+8 ≤ order) (aged : p+3 ≤ 3*k+2) (extra : q+2 ≤ p)
    (stamped : WilsonReceivedMeasuredStampPrice.opening R simple p order k deep aged zero_lt_one ≤ m+1)
    (test : Wallet actors) (degree a : ℕ) {cap:ℝ} (cn : 0 ≤ cap) {ε:ℝ} (ep:0<ε)
    (calendar:signed degree a p cap cn ≤ b) (close:PaceR.Close R degree cap m b)
    (adjacent:next ≤ b) (cold:cool ≤ b) (gate:(eventually_atTop.mp (usual p q ε ep)).choose ≤ b)
    (before:P₀.rent ≤ (g b)^p) :
    ∀ i (ib : i ≤ b) (mi : m ≤ i), ∃ L : P i mi (read i ib),
      WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
        mb source P₀ i mi (read i ib) L ∧
      (8*(Oak.expenseReal R hk D Q π Γ books mi L.op L.lesson ahead order shelf)^L.op.count)*L.rent
        ≤ ε*(g (i+1))^q := by
  intro i ib mi
  obtain ⟨L,trace,bill⟩:=WilsonReceivedCloseSignedPrice.paid R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats mb source P₀ course path top pass scroll chamber month hospital fits narrow load packed
    simple p deep aged zero_lt_one le_rfl stamped test degree a cn (η:=1) zero_lt_one calendar close i ib mi
  refine ⟨L,trace,?_⟩
  let quiet := (Stock.census V).quiet
  have noFee (w : V→ℝ) : Poly.toll w quiet=1 := by simp [Poly.toll,quiet,Census.quiet]
  let received := (8*(Oak.expenseReal R hk D Q π Γ books mi L.op L.lesson ahead order shelf)^L.op.count)*L.rent
  have heatPos : 0<g (i+1) := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson (by omega : i<N)))
  have fee₀ := bill quiet (by simp [quiet,Census.quiet]) received (by rw [noFee,one_mul]; exact le_add_of_nonneg_right (by positivity))
  have price : received ≤ (g b)⁻¹*(P₀.rent+2*(3*g b)^p) := by simpa only [noFee,one_mul,mul_one,Real.rpow_neg_one] using fee₀
  have low:=(eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose_spec b cold N per top.le
  have band:=WilsonReceivedCloseOrdinaryScale.inverse R simple (per:=per) ib top adjacent
  have paid:=(eventually_atTop.mp (usual p q ε ep)).choose_spec b gate N per top.le
  exact price.trans (scalar p q extra low.1 heatPos (by linarith only [low.1,low.2]) band before paid)

end Course
end YM.Integration.WilsonReceivedCloseRetainedRent
