import YM.Integration.WilsonRootedKioskPostRadius
import YM.Integration.WilsonMovingMentorIncomingSlots
import YM.Integration.WilsonOriginalReceivedPost
import YM.QuadraticLocal.Advent

/-! The two actual outgoing capture accounts, on their common original
marker radius and the original forced divisor, before the physical test. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCenteredIncomeRate
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

/-- Before the output is tested to any order, a fixed number of actual
incoming sources pays the whole joined regular wage. -/
theorem purchased (y : ℝ) (hy : y=R.alloy.B.a.clock.hatBeta (i+1)) (lower : 1≤y) (expense : Ω≤y) :
    account ≤ 25*y^(seats+1) := by
  let cash := P.issued.Waffle
  let cap := (fig).produce (sheet).ratio.count*P.cost
  have b₀ : 0 ≤ P.cost := budget_nonneg (P.salary.suggests 0)
  have enough : cap ≤ 1 := calc
    _ ≤ Ω*P.cost := mul_le_mul_of_nonneg_right cash.earns b₀
    _ ≤ Ω*Ω⁻¹ := mul_le_mul_of_nonneg_left P.affordable cash.paysAbove.le
    _ = _ := mul_inv_cancel₀ cash.paysAbove.ne'
  let due := Invoice.price (Ψ i).p (fig).mist (order+shelf+1) P.op.count width (fig).limitC G
  have salary : due*cap ≤ Ω :=
    (mul_le_of_le_one_right cash.minted.le enough).trans cash.quote
  have four:=cash.strong
  have one : 1≤Ω := by linarith
  have delivered : Ω⁻¹*P.rent ≤ 1 := by
    calc
      _ ≤ Ω⁻¹*1 := mul_le_mul_of_nonneg_left P.small (inv_nonneg.mpr cash.paysAbove.le)
      _ ≤ 1 := by simp only [mul_one];exact inv_le_one_of_one_le₀ one
  have young : Burn.young (R.alloy.B.a.clock.hatBeta (i+1)) k≤1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (hy ▸ lower)
    rw [Burn.sale_eq]
    have h : 0≤(Burn.horizon k:ℝ) := Nat.cast_nonneg _
    linarith
  have old : oldFee ≤ 24*Ω := by
    calc
      _ ≤ 8*Ω*(Ω⁻¹*P.rent+Burn.young (R.alloy.B.a.clock.hatBeta (i+1)) k+(fig).fidelity) := P.issued.effort
      _ ≤ 8*Ω*(1+1+1) := mul_le_mul_of_nonneg_left (by linarith only [delivered,young,cash.tenor.2]) (by positivity)
      _ = _ := by ring
  have spent : modelFee*((fig).produce (sheet).ratio.count*P.cost)+Ω^P.op.count*oldFee ≤ 25*Ω^(seats+1) := by
    have growing:=one_le_pow₀ one (n:=seats)
    have next : Ω≤Ω^(seats+1) := by rw [pow_succ];simpa using mul_le_mul_of_nonneg_right growing cash.paysAbove.le
    calc
      _ ≤ Ω+Ω^P.op.count*(24*Ω) := add_le_add salary (mul_le_mul_of_nonneg_left old (pow_nonneg cash.paysAbove.le _))
      _ ≤ _ := by rw [P.capacity];rw [pow_succ] at next ⊢;nlinarith only [next]
  have bound : (Ω^6)⁻¹≤1 := inv_le_one_of_one_le₀ (one_le_pow₀ one)
  calc
    _ ≤ (Ω^6)⁻¹ * (25*Ω^(seats+1)) := mul_le_mul_of_nonneg_left spent (inv_nonneg.mpr (pow_nonneg cash.paysAbove.le _))
    _ ≤ 1*(25*Ω^(seats+1)) := mul_le_mul_of_nonneg_right bound (by positivity)
    _ ≤ _ := by simp only [one_mul];exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ cash.paysAbove.le expense _) (by norm_num)

include course cut in
theorem original (simple : G.Simple) (late : (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ i)
    (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2) :
    account ≤ 25*(R.alloy.B.a.clock.hatBeta (i+1))^(seats+1) := by
  let iWalk := course.1.walk i hi cut.le
  let jWalk := course.1.walk (i+1) (Nat.le_succ_of_le hi) cut
  let y := R.alloy.B.a.clock.hatBeta (i+1)
  have window := (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose_spec i late
  have upper : 1 ≤ y := window.1.trans window.2.1
  let paidWalk := (WilsonMovingMentorIncomingSlots.original R course hi cut).2.2.choose
  letI : Countable P.modelIndex := P.modelCount
  have band : (Ψ (i+1)).beta ∈ Shoot.band R.alloy.B.a (i+1) := by
    rw [jWalk.beta]
    exact (R.makes.wilson.represents N per (i+1) cut).band
  have wallet := Mentor.Cruise.Semester.tight D R.rolls Q R.alloy R.kit φ books pass P.op
    (Oak.era R hk D Q π Γ hi P.op P.lesson) (R.alloy.B.a.S.oneStep i per).exact_size P.model order
    P.voter ahead jWalk.truep.point paidWalk iWalk.truep.point hospital load shelf narrow band
  have grain : Beaming.grain (R.alloy.B.a.clock.J i) ≤ 1 := by
    unfold Beaming.grain
    exact (div_le_one (by positivity)).mpr (by linarith only [Nat.cast_nonneg (α:=ℝ) (R.alloy.B.a.clock.J i)])
  have expense : Ω ≤ y := (wallet.1.trans (min_le_right ..)).trans
    ((Real.rpow_le_rpow_of_exponent_le upper grain).trans_eq (Real.rpow_one y))
  exact purchased R hk D Q π Γ Ψ books hi ahead actors pieces grades order shelf seats physical P y rfl upper expense

end YM.Integration.WilsonCenteredIncomeRate
