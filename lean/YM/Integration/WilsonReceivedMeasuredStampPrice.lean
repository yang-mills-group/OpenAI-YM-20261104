import YM.Integration.WilsonOriginalSignedQFiled
import YM.Integration.WilsonMovingMentorIncomingSlots
import YM.Integration.WilsonOriginalCompensatedTuition

/-! The signed charge for restoring a deposited source to the measured
coupling at the next original block. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedMeasuredStampPrice
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Stationary Comparison.RG02 QuadraticLocal.Rebirth ConnectedActivityE6 Pressure
open QuadraticLocal.Affinity
open scoped Classical BigOperators

def opening {G : Gauge} (R : Run G) (simple : G.Simple) (q order k : ℕ)
    (deep : 2*q+8 ≤ order) (aged : q+3 ≤ 3*k+2) {ε : ℝ} (ep : 0<ε) : ℕ :=
  (eventually_atTop.mp (WilsonOriginalCompensatedTuition.salary R simple q order k deep aged (half_pos ep))).choose

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (hi : m ≤ i) (cut : i < N)
  (op : Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson : Lesson (N:=N) R hk D Q π Γ hi)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V ι : Type} [Fintype V] [DecidableEq V] {X : V → Type} [Countable ι]
  {passport : Earn.Passport (R.family.side (i+1) per) V}
  (actors : ∀ v, Set (X v)) (M : ι → Row passport (Stock.census V) G (Affinity.Wallet actors))
  (order shelf : ℕ)
  (voter : Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
    order op.count op.stage k (R.alloy.B.a.clock.J i))

local notation "siz" => (R.alloy.B.a.S.oneStep i per).exact_size
local notation "sp" => (Pane.panel R.alloy i siz).ratio.count
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "upper" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "δ" => Burn.young upper k
local notation "gf" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "stampFee" => Invoice.price (Ψ i).p (fig).mist (order+shelf+1) op.count ((Ψ i).p.supportExponent+1+1) (fig).limitC G

include course cut voter in
theorem original (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf ≤ R.alloy.B.a.clock.J i) (load : op.count ≤ Burn.horizon k+2) (simple : G.Simple)
    (q : ℕ) (deep : 2*q+8 ≤ order) (aged : q+3 ≤ 3*k+2) {ε : ℝ} (ep : 0 < ε)
    (late : opening R simple q order k deep aged ep ≤ i)
    {b e : ℝ} (b₀ : 0 ≤ b) (bp : b ≤ Ω⁻¹) (e₀ : 0 ≤ e) :
    let wallet := (fig).produce sp*b
    let residue := (fig).hitPrice G sp (Ψ (i+1)).p (Ψ i).p b e δ oldG
    (fig).fidelity*stampFee*wallet+residue ≤ 8*Ω*e+ε*gf^q := by
  intro wallet residue
  let paidWalk := (WilsonMovingMentorIncomingSlots.original R course hi cut).2.2.choose
  have fine : (Ψ (i+1)).beta ∈ Shoot.band R.alloy.B.a (i+1) := by
    rw [(course.1.walk (i+1) (Nat.le_succ_of_le hi) cut).beta]
    exact (R.makes.wilson.represents N per (i+1) cut).band
  have bought := Mentor.Cruise.Semester.tight D R.rolls Q R.alloy R.kit φ books pass op
    (Oak.era R hk D Q π Γ hi op lesson) siz M order voter ahead
    (course.1.walk (i+1) (Nat.le_succ_of_le hi) cut).truep.point paidWalk
    (course.1.walk i hi cut.le).truep.point hospital load shelf narrow fine
  have cash := bought.2
  have os : 0 < Ω := cash.paysAbove
  have cb : wallet ≤ 1 := calc
    _ ≤ Ω*b := mul_le_mul_of_nonneg_right cash.earns b₀
    _ ≤ Ω*Ω⁻¹ := mul_le_mul_of_nonneg_left bp os.le
    _ = 1 := mul_inv_cancel₀ os.ne'
  have upper₀ : 0 ≤ upper := zero_le_one.trans (R.alloy.B.a.fits.delayed _).le
  have young₀ : 0 ≤ δ := Real.rpow_nonneg upper₀ _
  have fi := cash.bloom
  have carry : residue ≤ 8*Ω*(e+δ+(fig).fidelity) :=
    cash.spend b₀ (bp.trans (inv_le_one_of_one_le₀ cash.cool)) young₀ e₀
  have invoice : stampFee*wallet ≤ Ω := calc
    _ ≤ stampFee*1 := mul_le_mul_of_nonneg_left cb cash.minted.le
    _ ≤ _ := by rw [mul_one]; exact cash.quote
  have small := (eventually_atTop.mp (WilsonOriginalCompensatedTuition.salary R simple q order k deep aged (half_pos ep))).choose_spec
    i late N per cut Ω os (bought.1.trans (min_le_right ..))
  have reserve : 0 ≤ Ω⁻¹*upper^(-(order:ℝ)) := mul_nonneg (inv_nonneg.mpr os.le) (Real.rpow_nonneg upper₀ _)
  have fresh : 8*Ω*(δ+(fig).fidelity) ≤ (ε/2)*gf^q := calc
    _ ≤ 8*Ω*(Ω⁻¹*upper^(-(order:ℝ))+δ+(fig).fidelity) :=
      mul_le_mul_of_nonneg_left (by linarith only [reserve]) (by positivity)
    _ ≤ _ := small
  have stamp : (fig).fidelity*stampFee*wallet ≤ 8*Ω*(δ+(fig).fidelity) := calc
    _ ≤ (fig).fidelity*Ω := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left invoice fi.le
    _ ≤ _ := by nlinarith only [mul_nonneg os.le young₀,mul_nonneg os.le fi.le]
  calc
    _ ≤ (ε/2)*gf^q+8*Ω*(e+δ+(fig).fidelity) := add_le_add (stamp.trans fresh) carry
    _ = 8*Ω*e+((ε/2)*gf^q+8*Ω*(δ+(fig).fidelity)) := by ring
    _ ≤ 8*Ω*e+((ε/2)*gf^q+(ε/2)*gf^q) := add_le_add le_rfl (add_le_add le_rfl fresh)
    _ = _ := by ring

end YM.Integration.WilsonReceivedMeasuredStampPrice
