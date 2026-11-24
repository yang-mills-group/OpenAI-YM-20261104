import YM.Integration.WilsonThermometerCourseHearing

/-! The actual before-field earnings of the three registered physical letters. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerCompulsoryIntake
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
open Progress.DirectedRecipe QuadraticLocal.Tint

local instance : Countable P.modelIndex := P.modelCount
local notation "upper" => Ψ (i+1)
local notation "lower" => Ψ i
local notation "picture" => Tint.Patrol.picture P.model P.input
local notation "reserve" => LocalComparison.forcedDivisor R.family (i+1)

/-- A paid intake with all original addresses and the original compulsory allowance. -/
theorem sealed [Countable P.inputIndex] : Nonempty (Travel.Seal picture P.w 2 reserve) := by
  have costPos := Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0)
  have paid := P.issued.Waffle.converted costPos P.affordable
  have old := Lamps.tenure _ P.w P.salary.positive P.regular (show
    (upper).p.supportExponent ≤ (upper).p.supportExponent+1+1 from by linarith)
  obtain ⟨B,_⟩ := Campus.Investor.pays P.model P.input P.w P.salary.positive ages P.salary paid.breeze
    (show _ ≤ 2-P.rent from paid.fits.trans (by linarith [P.small]))
    ((mul_le_of_le_one_left (by positivity) paid.fits).trans paid.past) old P.forced
  exact ⟨B⟩

/-- The cash and its high-order rooted hearing are issued on one literal nonbare
block, by the selected physical course and the same stage used by its marked post. -/
theorem appointed (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (pass : AllOrder.Transit.Pass D Q R.alloy R.kit)
    (training : Mentor.Educated D R.rolls Q R.kit.shape R.kit.scout φ books R.alloy.delay) :
    ∃ (schedule : Oak.Calendar (N:=N) R hk D Q π Γ Ψ floor P.lesson)
      (staff : Mentor.Employees D R.rolls Q R.alloy R.kit φ books P.op (R.alloy.B.a.S.oneStep i per).exact_size N schedule.clock lower),
      staff.real.height = P.op.stage := by
  obtain ⟨schedule⟩ := Oak.agrees R hk D Q π Γ Ψ course floor live P.lesson
  have top := QuadraticLocal.Advent.later R π Γ Ψ course (floor.trans (Nat.le_succ i)) live
  have base := QuadraticLocal.Advent.later R π Γ Ψ course floor live.le
  have band : (upper).beta ∈ Shoot.band R.alloy.B.a (i+1) := by
    rw [top.beta]
    exact (R.T.sticks N per |>.prices _ (Nat.zero_le _) live).2
  obtain ⟨staff⟩ := Mentor.crew D R.rolls Q R.alloy R.kit φ books pass training
    P.op (R.alloy.B.a.S.oneStep i per).exact_size (upper).beta band live lower base.truep.point top.truep.point rfl schedule.clock
  exact ⟨schedule,staff,staff.paid.1⟩

end YM.Integration.WilsonThermometerCompulsoryIntake
end
