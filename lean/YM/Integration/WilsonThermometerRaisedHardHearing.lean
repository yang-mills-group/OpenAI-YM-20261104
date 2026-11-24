import YM.Integration.WilsonThermometerRaisedHardSeals
import YM.Integration.WilsonReceivedCompulsoryRate

/-! Both hard variations have the original upper vacuum, its real calendar and its other marked entries. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRaisedHardHearing
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

theorem original (K₀ K₁ : hardSlot)
    (bound₀ : K₀.Paid P.w (upper).p.B (upper).p.supportExponent 1)
    (bound₁ : K₁.Paid P.w (upper).p.B (upper).p.supportExponent 1)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (pass : AllOrder.Transit.Pass D Q R.alloy R.kit)
    (training : Mentor.Educated D R.rolls Q R.kit.shape R.kit.scout φ books R.alloy.delay)
    (q : ℕ) (enrolled : q ≤ P.op.stage) :
    ∃ (W : schedule) (T₀ : Travel.Seal (gallery K₀) P.w 2 1)
      (T₁ : Travel.Seal (gallery K₁) P.w 2 1) (a : HasSlots (upper).p (upper).activities),
      WilsonReceivedCompulsoryRate.atOrder (k:=P.op.count) (P':=(lower))
        W.clock (gallery K₀) P.w T₀ P.salary.positive a fired q ∧
      WilsonReceivedCompulsoryRate.atOrder (k:=P.op.count) (P':=(lower))
        W.clock (gallery K₁) P.w T₁ P.salary.positive a fired q := by
  obtain ⟨W,E,high⟩ := WilsonThermometerCompulsoryIntake.appointed
    R A simple live o hk D Q π Γ Ψ books ahead order shelf seats floor P course pass training
  obtain ⟨T₀⟩ := WilsonThermometerRaisedHardSeals.sealed R A simple live o hk D Q π Γ Ψ books ahead order shelf seats floor P K₀ bound₀
  obtain ⟨T₁⟩ := WilsonThermometerRaisedHardSeals.sealed R A simple live o hk D Q π Γ Ψ books ahead order shelf seats floor P K₁ bound₁
  have slots₁ := QuadraticLocal.Advent.spare R π Γ Ψ course (floor.trans (Nat.le_succ i)) live
  have room : 2*(2+(1:ℝ)) ≤ Mentor.capDay := by norm_num [Mentor.capDay]
  exact ⟨W,T₀,T₁,slots₁,
    WilsonReceivedCompulsoryRate.through W.clock E.real (gallery K₀) P.w T₀
      P.salary.positive slots₁ room fired (enrolled.trans_eq high.symm) P.issued.Waffle.breeze.2.1,
    WilsonReceivedCompulsoryRate.through W.clock E.real (gallery K₁) P.w T₁
      P.salary.positive slots₁ room fired (enrolled.trans_eq high.symm) P.issued.Waffle.breeze.2.1⟩

end YM.Integration.WilsonThermometerRaisedHardHearing
end
