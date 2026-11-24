import YM.Integration.WilsonOriginalReceivedPost
import YM.QuadraticLocal.Advent

/-! The two actual outgoing capture accounts, on their common original
marker radius and the original forced divisor, before the physical test. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCenteredReceivedWages
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open scoped Classical BigOperators Topology
open Push.AbsoluteSums

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

local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "gauge" => (Tint.Patrol.report student P.output oldG)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "width" => ((Ψ i).p.supportExponent+1+1)
local notation "modelFee" => Invoice.price (Ψ i).p (fig).mist (order+shelf+1) P.op.count width (fig).limitC G
local notation "oldFee" => Earn.Earnings.hitPrice (fig) G (sheet).ratio.count (Ψ (i+1)).p (Ψ i).p
  (Ω⁻¹*P.cost) (Ω⁻¹*P.rent) (Burn.young (R.alloy.B.a.clock.hatBeta (i+1)) k) oldG
local notation "account" => (Ω^6)⁻¹*(modelFee*((fig).produce (sheet).ratio.count*P.cost)+Ω^P.op.count*oldFee)
local notation "weights" => Stoop.radius P.w (Ω^6)

include course cut in
theorem original (way : WayStation R.kit) :
    (∀ i,0<weights i) ∧ (gauge).E.Paid weights (Ψ i).p.B ((Ψ i).p.supportExponent+2) account ∧
      (gauge).K.Paid weights (Ψ i).p.B (Ψ i).p.supportExponent κ := by
  have positive:=P.issued.earning.positive
  have four:=P.issued.Waffle.strong
  have one : 1≤Ω^6:=one_le_pow₀ (show 1≤Ω by linarith only [four])
  have analytic:=QuadraticLocal.Earn.Scene.Armada.paid student P.w grades P.issued.earning (Ψ i).p P.issued.Waffle.soon
  have together:=Lamps.joinPaid analytic P.issued.tuition
  have smaller:=Stoop.tighten P.w _ positive one together
  have flag:=QuadraticLocal.Advent.force_bill R way π Γ Ψ course hi cut (Nat.zero_le _)
  simp only [Nat.cast_zero,neg_zero,Real.rpow_zero,one_mul] at flag
  refine ⟨fun j=>div_pos (positive _) (zero_lt_one.trans_le one),?_,?_⟩
  · rw [show (gauge).E=(lamps).join P.output.old from rfl]
    simpa only [add_assoc,one_add_one_eq_two] using smaller
  exact P.output.hard.mono P.issued.kept flag

end YM.Integration.WilsonCenteredReceivedWages
