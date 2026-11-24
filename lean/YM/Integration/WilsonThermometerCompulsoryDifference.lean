import YM.Integration.WilsonReceivedCompulsoryPairing
import YM.Integration.WilsonReceivedCompulsoryScaled
import YM.Integration.WilsonThermometerRaisedHardHearing
import YM.Integration.WilsonThermometerRaisedHardSeals
import YM.Integration.WilsonReceivedCompulsoryRate

/-! Both hard variations have the original upper vacuum, its real calendar and its other marked entries. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerCompulsoryDifference
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

local notation "quote" => Time.quoteHard R.alloy.B.a (i+1) R.kit.book (Ψ ((i+1)+1)).beta

/-- On one nonbare original seven-face source, both full hard returns receive
one rooted signed comparison at every funded moving derivative. The true
geometric factor may be restored on each original support. -/
theorem original (way : WayStation R.kit) (finer : i+1<N) (K₀ K₁ : hardSlot)
    (bound₀ : K₀.Paid P.w (upper).p.B (upper).p.supportExponent quote)
    (bound₁ : K₁.Paid P.w (upper).p.B (upper).p.supportExponent quote)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (pass : AllOrder.Transit.Pass D Q R.alloy R.kit)
    (training : Mentor.Educated D R.rolls Q R.kit.shape R.kit.scout φ books R.alloy.delay)
    (q : ℕ) (enrolled : q ≤ P.op.stage) :
    ∃ (W : schedule) (T : Travel.Seal (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w 2 (1+1))
      (a : HasSlots (upper).p (upper).activities), ∀ (t : Wallet disks) (scale : ℝ), 0 ≤ scale →
      WilsonReceivedCompulsoryScaled.atOrder (k:=P.op.count) (P':=(lower))
        W.clock (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w T P.salary.positive a (false,t) (false,t) (true,t) scale q := by
  have paid:=QuadraticLocal.Advent.force_bill R way π Γ Ψ course (floor.trans (Nat.le_succ i)) finer (Nat.zero_le _)
  have allowance : quote ≤ LocalComparison.forcedDivisor R.family (i+1) := by
    simpa only [Nat.cast_zero,neg_zero,Real.rpow_zero,one_mul] using paid
  have cap : LocalComparison.forcedDivisor R.family (i+1) ≤ 1 :=
    Real.sqrt_le_one.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _)))
  obtain ⟨W,E,high⟩ := WilsonThermometerCompulsoryIntake.appointed
    R A simple live o hk D Q π Γ Ψ books ahead order shelf seats floor P course pass training
  obtain ⟨T₀⟩ := WilsonThermometerRaisedHardSeals.sealed R A simple live o hk D Q π Γ Ψ books ahead order shelf seats floor P K₀ (Hard.mono _ bound₀ (allowance.trans cap))
  obtain ⟨T₁⟩ := WilsonThermometerRaisedHardSeals.sealed R A simple live o hk D Q π Γ Ψ books ahead order shelf seats floor P K₁ (Hard.mono _ bound₁ (allowance.trans cap))
  have slots₁ := QuadraticLocal.Advent.spare R π Γ Ψ course (floor.trans (Nat.le_succ i)) live
  obtain ⟨T⟩ := WilsonReceivedCompulsoryPairing.sealed (Tint.Patrol.picture P.model P.input).E
    K₀ K₁ P.w P.salary.positive T₀ T₁
  have room : 2*(2+(1+(1:ℝ))) ≤ Mentor.capDay := by norm_num [Mentor.capDay]
  refine ⟨W,T,slots₁,fun t scale nonnegative => ?_⟩
  have signed := WilsonReceivedCompulsoryDifference.original (k:=P.op.count) (P':=(lower))
    W.clock E.real (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w T P.salary.positive slots₁ room
    (false,t) (false,t) (true,t)
    (WilsonReceivedCompulsoryPairing.regular (Tint.Patrol.picture P.model P.input).E K₀ K₁
      P.w P.salary.positive T slots₁ t)
    (enrolled.trans_eq high.symm) P.issued.Waffle.breeze.2.1
  exact WilsonReceivedCompulsoryScaled.weighted W.clock (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w T P.salary.positive
    slots₁ (false,t) (false,t) (true,t) signed scale nonnegative

end YM.Integration.WilsonThermometerCompulsoryDifference
end
