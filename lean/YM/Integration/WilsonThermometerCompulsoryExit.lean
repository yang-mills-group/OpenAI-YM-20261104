import YM.Integration.WilsonThermometerCourseHearing
import YM.Integration.WilsonMovingMentorStartingHard

/-! The compulsory exit of the original seven-face deposited thermometer. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerCompulsoryExit
open FVA1 Finset Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter OriginalForcedAddresses
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonThermometerCourseIntake
open scoped Classical BigOperators Topology
open WilsonThermometerCourseHearing
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
    {m N per k i : ℕ} (live : i < N) (o : Positions (Fin 3) (R.family.side N per))
    (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
    (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
    {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
    (ahead : Mentor.Forecast D R.rolls Q φ books) (order shelf seats : ℕ) (floor : m ≤ i)
local notation "ages" => (fun u : Fin 3 => (grade u).val)
variable (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead disks sectors ages
  order shelf seats i floor (offered R A simple live o))
local notation "heat" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "divisor" => LocalComparison.forcedDivisor R.family i
local notation "expense" => Oak.expenseReal R hk D Q π Γ books floor P.op P.lesson ahead order shelf
local notation "quoted" => Time.quoteHard R.alloy.B.a i R.kit.book (Ψ (i+1)).beta

private theorem restore (x κ : ℝ) (hx : 0 < x) (q n : ℕ) :
    (x^6)^n*(x^(-((q+6*n:ℕ):ℝ))*κ) = x^(-(q:ℝ))*κ := by
  rw [← pow_mul, Real.rpow_neg hx.le, Real.rpow_natCast, Real.rpow_neg hx.le, Real.rpow_natCast, pow_add]
  field_simp

/-- All hard keys of this same measured seven-face return at the original test radii
admit one common hard divisor and the requested remaining order. -/
theorem original (way : WayStation R.kit) (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (q : ℕ) (active : q+6*seats ≤ R.alloy.B.a.clock.J i) :
    P.output.hard.Paid P.w (Ψ i).p.B (Ψ i).p.supportExponent (heat^(-(q:ℝ))*divisor) := by
  have x₁ : 1 ≤ heat := (R.alloy.B.a.fits.delayed _).le
  have xpos : 0 < heat := zero_lt_one.trans_le x₁
  have g₁ : Beaming.grain (R.alloy.B.a.clock.J i) ≤ 1 := by
    unfold Beaming.grain
    apply (div_le_one (by positivity)).2
    linarith [Nat.cast_nonneg (α:=ℝ) (R.alloy.B.a.clock.J i)]
  have cap : expense ≤ heat := calc
    _ ≤ budgetR R i := P.issued.Beamwork
    _ ≤ heat^(Beaming.grain (R.alloy.B.a.clock.J i)) := min_le_right _ _
    _ ≤ heat^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le x₁ g₁
    _ = _ := Real.rpow_one _
  have e₀ : 0 ≤ expense := (by norm_num : (0:ℝ)≤4).trans P.issued.Waffle.strong
  have rebate := QuadraticLocal.Advent.force_bill R way π Γ Ψ course floor live active
  change quoted ≤ heat^(-((q+6*seats:ℕ):ℝ))*divisor at rebate
  have reserve : (expense^6)^P.op.count*quoted ≤ heat^(-(q:ℝ))*divisor := calc
    _ ≤ (heat^6)^P.op.count*(heat^(-((q+6*seats:ℕ):ℝ))*divisor) := by
      apply mul_le_mul (pow_le_pow_left₀ (pow_nonneg e₀ _) (pow_le_pow_left₀ e₀ cap _) _) rebate
      · exact (Real.exp_pos _).le
      · positivity
    _ = _ := by
      rw [P.capacity]
      exact restore _ _ xpos q seats
  exact QuadraticLocal.Hard.mono _ P.issued.paidForce reserve

/-- The fully restored hard book has the same complete original physical output
at each held field and each of the seven faces. -/
theorem returned :
    (Tint.Patrol.report (Oak.student (n:=per) R hk D Q π Γ books floor P.op P.lesson ahead
      disks P.model order P.voter) P.output (Coat.gStep (Ψ (i+1)).beta)).density fired =
      incoming R A simple live.le o := by
  rw [← WilsonOriginalReceivedChain.report, fired_input, WilsonThermometerCourseIntake.step]

end YM.Integration.WilsonThermometerCompulsoryExit
end
