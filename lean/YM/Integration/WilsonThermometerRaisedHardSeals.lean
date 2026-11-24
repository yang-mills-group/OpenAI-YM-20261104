import YM.Integration.WilsonThermometerCompulsoryIntake

/-! Both hard variations have the original upper vacuum, its real calendar and its other marked entries. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRaisedHardSeals
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
open Progress.DirectedRecipe QuadraticLocal.Tint

local instance : Countable P.modelIndex := P.modelCount
local notation "upper" => Ψ (i+1)
local notation "lower" => Ψ i
local notation "schedule" => Oak.Calendar (N:=N) R hk D Q π Γ Ψ floor P.lesson
local notation "hardSlot" => Hard (Wallet disks) (upper).p (upper).activities.forced
  (upper).activities.K P.passport.origin (Stock.census (Fin 3))
local notation "withHard" A => ({ P.input with hard := A })
local notation "gallery" A => (Tint.Patrol.picture P.model (withHard A))
variable [Countable P.inputIndex]

theorem sealed (K : hardSlot) (budget : K.Paid P.w (upper).p.B (upper).p.supportExponent 1) :
    Nonempty (Travel.Seal (gallery K) P.w 2 1) := by
  have pos := Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0)
  have paid := P.issued.Waffle.converted pos P.affordable
  have old := Lamps.tenure _ P.w P.salary.positive P.regular (show
    (upper).p.supportExponent ≤ (upper).p.supportExponent+1+1 from by linarith)
  obtain ⟨B,_⟩ := Tint.Campus.Investor.pays P.model (withHard K) P.w P.salary.positive ages P.salary
    paid.breeze (show _ ≤ 2-P.rent from paid.fits.trans (by linarith [P.small]))
    ((mul_le_of_le_one_left (by positivity) paid.fits).trans paid.past) old budget
  exact ⟨B⟩

end YM.Integration.WilsonThermometerRaisedHardSeals
end
