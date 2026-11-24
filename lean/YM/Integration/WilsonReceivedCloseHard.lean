import YM.Integration.WilsonReceivedCloseCash
import YM.Integration.WilsonReceivedClosePrices
/-! On the returned physical post the same full majorizing polynomial funds every marked forced coefficient at its actual support and arity. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedCloseHard
open private restore from YM.Integration.WilsonReceivedCloseCash
open private scales from YM.QuadraticLocal.Pry
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


theorem roster (returned : received) :
    ∃ pay : ℕ → Poly marks, (∀ j t U, Push.Corrected.Width.Covered (Y.hard.hard t j U) (pay j)) ∧
      ∀ s : marks.Mode, Ac.Hit (fun j=>((Ψ i).activities.forced j).support) (Ψ i).p.B
        (fun j=> Poly.toll w s * ‖(pay j).part s‖) (Ψ i).p.supportExponent
        (((Ω)^6)^s.val.card * quoteR R (Ψ (i+1)).beta i) := by
  obtain ⟨pay, held, covered⟩ := returned.kept.wages
  refine ⟨pay, held, ?_⟩
  intro s
  have os : 0 < Ω := zero_lt_one.trans_le returned.Waffle.cool
  have pos : 0 < (Ω)^6 := pow_pos os _
  let radius := Stoop.radius w ((Ω)^6)
  have radiuspos : ∀ j, 0 < radius j := fun j => div_pos (returned.earning.positive j) pos
  apply scales _ covered (fun j=>mul_nonneg (Poly.worth returned.earning.positive _).le (norm_nonneg _))
  · intro j
    rw [restore pos w s,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg pos.le _)
    exact Finset.single_le_sum (fun t (_:t ∈ Finset.univ)=>mul_nonneg (Poly.worth radiuspos t).le (norm_nonneg _))
       (Finset.mem_univ s)
  · exact pow_nonneg pos.le _

end YM.Integration.WilsonReceivedCloseHard
