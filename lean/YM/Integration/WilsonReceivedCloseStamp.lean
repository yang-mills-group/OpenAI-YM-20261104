import YM.Integration.WilsonReceivedMeasuredStampPrice

/-! The restored old salary is paid on the same measured continuation as the newly filed row. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseStamp
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Stationary Comparison.RG02 QuadraticLocal.Rebirth ConnectedActivityE6 Pressure
open QuadraticLocal.Affinity
open scoped Classical BigOperators

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
local notation "rebate" => Oak.rebate R hk D Q π Γ hi op lesson

include course cut voter in
theorem original (scroll : VowsR.LawScroll G φ)
    (employed : VowsR.Chamber scroll R.kit D Q books)
    (month : Rebirth.Scholar.Month R.rolls D Q R.alloy.delay)
    (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (rank : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J i)
    (load : op.count ≤ Burn.horizon k+2) {b : ℝ} (b₀ : 0 ≤ b) (bp : b ≤ Ω⁻¹) :
    rebate*((fig).produce sp*b) ≤ budgetR R i := by
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
  have cb : (fig).produce sp*b ≤ 1 := calc
    _ ≤ Ω*b := mul_le_mul_of_nonneg_right cash.earns b₀
    _ ≤ Ω*Ω⁻¹ := mul_le_mul_of_nonneg_left bp os.le
    _ = 1 := mul_inv_cancel₀ os.ne'
  obtain ⟨credit,within⟩ := Oak.credited R hk D Q π Γ Ψ course scroll books employed
    hi cut op lesson ahead month order shelf rank narrow
  have rebate₀ : 0 ≤ rebate :=
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans credit.quota)).trans credit.attendance
  exact (mul_le_mul_of_nonneg_left cb rebate₀).trans (by simpa only [mul_one] using within)

end YM.Integration.WilsonReceivedCloseStamp
