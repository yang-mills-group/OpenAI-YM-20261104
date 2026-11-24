import YM.Integration.WilsonCapturedStudentAngularWage
import YM.Integration.WilsonOriginalMeasuredReentry

/-! Rooted expenditure for the complete source at the dated nonlinear reset. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalRestampedSourceIncome
open Function Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler AllOrder.Transit.WheelP
open QuadraticLocal.Rebirth QuadraticLocal.Affinity WilsonOriginalReceivedChain Stationary Multi
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open AnalyticBridge VerifiedReset RemainderComparison
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {m N per k i : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (hi : m ≤ i)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i hi physical)

local notation "stud" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors P.model order P.voter
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "op" => R.family.path.levels.clock.op i per
local notation "stipend" => (fig).produce (op).ratio.count*P.cost
local notation "markUp" => Oak.rebate R hk D Q π Γ hi P.op P.lesson
local notation "rooted" => Mutation.stamp stud (Γ i) (Oak.grade0 R hk D Q π Γ hi P.lesson)
  (Burn.horizon k+2) order



theorem original (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (cut : i < N) (pass : Pass D Q R.alloy R.kit)
    (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (fits : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J i) :
    Scene.Armada (rooted) P.w grades σ ((markUp)*(stipend)) order P.op.count shelf ∧
    0 < σ ∧ 0 ≤ (markUp)*(stipend) ∧ (markUp)*(stipend) ≤ budgetR R i := by
  obtain ⟨credit, affordable⟩ := WilsonOriginalMeasuredReentry.credited R hk D Q pass π Γ Ψ course
    hi cut P.lesson books P.op ahead month order shelf fits narrow
  have priced := Mutation.allocate (stud) (Γ i) (Oak.grade0 R hk D Q π Γ hi P.lesson)
    (Burn.horizon k+2) order P.w grades credit P.issued.earning
  have monotone : 0 ≤ (markUp) :=
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans credit.quota)).trans credit.attendance
  refine ⟨priced, Poetry.Agenda.stem .., Push.AbsoluteSums.budget_nonneg (priced.suggests (0 : Site _)),?_⟩
  calc
    (markUp)*(stipend) ≤ (markUp)*1 :=
      mul_le_mul_of_nonneg_left (WilsonCapturedStudentAngularWage.stipend_le R hk D Q π Γ Ψ books
        ahead actors pieces grades order shelf seats hi physical P) monotone
    _ ≤ budgetR R i := by simpa only [mul_one] using affordable

end YM.Integration.WilsonOriginalRestampedSourceIncome
