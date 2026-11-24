import YM.Integration.WilsonFirstReceivedEarnedFee
import YM.Integration.WilsonOriginalCompensatedTuition
import YM.QuadraticLocal.Union.Return

/-! The old regular price on the original funded post, at the reporter's full
marked radii and the actual fine coupling. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedInheritedFee
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset
open Filter ConnectedActivityE6
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (hi : m ≤ i) (cut : i < N)
  (op : Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson : Lesson (N:=N) R hk D Q π Γ hi)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V ι : Type} [Fintype V] [DecidableEq V] {marks : Census V} {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  {passport : Earn.Passport (R.family.side (i+1) per) V}
  (actors : ∀ v, Set (X v)) (M : ι → Row passport marks G (Affinity.Wallet actors))
  (w : V → ℝ) (grades : V → ℕ) (order shelf : ℕ)
  (voter : Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
    order op.count op.stage k (R.alloy.B.a.clock.J i))
variable (cost:ℝ) {old next:Type}(pieces:∀ v,Submodule ℝ (X v))
  (Z:Tint.Incoming passport (Ψ (i+1)) (Affinity.Wallet actors) old marks)
  (rent:ℝ) (Y:Tint.Incoming (passport.coarser (R.family.path.levels.clock.op i per).ratio)
      (Ψ i) (Affinity.Wallet actors) next marks)
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "upper" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "oldFee" => Earn.Earnings.hitPrice (fig) G
  (R.family.path.levels.clock.op i per).ratio.count (Ψ (i+1)).p (Ψ i).p
  (Ω⁻¹*cost) (Ω⁻¹*rent) (Burn.young upper k) (Coat.gStep (Ψ (i+1)).beta)
local notation "received" => Oak.Buffered.SuccessStory R hk D Q π Γ Ψ books hi op lesson ahead
  actors pieces M Z w grades order shelf voter rent cost Y

open Pressure

include cut in
/-- The previously deposited regular debt propagates linearly through the true
return. All newly incurred regular charges are paid at the requested order. -/
theorem original (returned : received) (simple : G.Simple) (p : ℕ)
    (deep : 2*(p+1)+8 ≤ order) (aged : p+4 ≤ 3*k+2) {ε : ℝ} (positive : 0 < ε)
    (opened : WilsonFirstReceivedEarnedFee.opening R simple op.count p order k deep aged positive ≤ i) :
    Ω^op.count * oldFee ≤ (8*Ω^op.count)*rent +
      ε*(Coat.gStep (R.family.path.rep N per (i+1)).beta)^p := by
  let g := Coat.gStep (R.family.path.rep N per (i+1)).beta
  have os : 0 < Ω := lt_of_lt_of_le zero_lt_one returned.Waffle.cool
  have width := returned.Beamwork.trans (min_le_right ..)
  have paid := WilsonOriginalCompensatedTuition.salary R simple (p+1) order k deep (by omega)
    (show (0:ℝ) < 1 by norm_num)
  have refund := WilsonMovingMentorPageCoupling.repaid R simple op.count p positive
  have dates := max_le_iff.mp opened
  have pre := (eventually_atTop.mp paid).choose_spec i dates.1 N per cut Ω os width
  have post := (eventually_atTop.mp refund).choose_spec i dates.2 Ω os.le width N per cut
  have fidelity : (fig).fidelity =
      (betaF G (R.alloy.B.a.clock.hatBeta i) (R.rolls.L (R.alloy.B.a.clock.J (i+1)))) ^
      Mentor.Tuition.need order (Mentor.Tolerance (R.alloy.B.a.clock.J i)) := rfl
  let fresh := Burn.young upper k + (fig).fidelity
  have reserve : 0 ≤ Ω⁻¹*upper^(-(order:ℝ)) := mul_nonneg (inv_nonneg.mpr os.le) (Real.rpow_nonneg
    (le_trans zero_le_one (R.alloy.B.a.fits.delayed _).le) _)
  have newBill : 8*Ω*fresh ≤ g^(p+1) := by
    calc
      _ ≤ 8*Ω*(Ω⁻¹*upper^(-(order:ℝ))+Burn.young upper k+(fig).fidelity) :=
        mul_le_mul_of_nonneg_left (by dsimp only [fresh]; linarith only [reserve]) (by positivity)
      _ ≤ _ := by rw [fidelity]; simpa only [one_mul] using pre
  have carried : oldFee ≤ 8*rent+g^(p+1) := by
    refine returned.effort.trans ?_
    calc
      _ = 8*rent+8*Ω*fresh := by dsimp only [fresh]; field_simp [os.ne']; ring
      _ ≤ _ := add_le_add le_rfl newBill
  calc
    _ ≤ Ω^op.count * (8*rent+g^(p+1)) := mul_le_mul_of_nonneg_left carried (pow_nonneg os.le _)
    _ = (8*Ω^op.count)*rent + Ω^op.count*g^(p+1) := by ring
    _ ≤ _ := add_le_add le_rfl post

end YM.Integration.WilsonReceivedInheritedFee
