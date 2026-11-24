import YM.Integration.WilsonThermometerCompulsoryDifference
import YM.Integration.WilsonReceivedCompulsoryFaces
import YM.Integration.WilsonReceivedCompulsoryPairing
import YM.Integration.WilsonReceivedCompulsoryScaled
import YM.Integration.WilsonThermometerRaisedHardHearing
import YM.Integration.WilsonThermometerRaisedHardSeals
import YM.Integration.WilsonReceivedCompulsoryRate

/-! Both hard variations have the original upper vacuum, its real calendar and its other marked entries. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerCompulsoryLog
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

/-- The same physical calendar pays the signed moving derivatives and the
actual occupied native logarithm on every held Wilson configuration. -/
theorem original (way : WayStation R.kit) (finer : i+1<N) (K₀ K₁ : hardSlot)
    (bound₀ : K₀.Paid P.w (upper).p.B (upper).p.supportExponent quote)
    (bound₁ : K₁.Paid P.w (upper).p.B (upper).p.supportExponent quote)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (pass : AllOrder.Transit.Pass D Q R.alloy R.kit)
    (training : Mentor.Educated D R.rolls Q R.kit.shape R.kit.scout φ books R.alloy.delay)
    (q : ℕ) (enrolled : q ≤ P.op.stage) :
    ∃ (W : schedule) (T : Travel.Seal (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w 2 (1+1))
      (a : HasSlots (upper).p (upper).activities), ∀ (t : Wallet disks) (θ : ℝ), 0 ≤ θ →
      WilsonReceivedCompulsoryScaled.atOrder (k:=P.op.count) (P':=(lower))
        W.clock (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w T P.salary.positive a (false,t) (false,t) (true,t) θ q ∧
      ∀ (F : Config G (R.family.side i per)) (s : (Stock.census (Fin 3)).Mode) (v : Fin 3), v ∈ s.val →
        let field := fun x : Bool × Wallet disks => (WilsonReceivedCompulsoryFaces.markedLog
          (k:=P.op.count) (P':=(lower)) W.clock (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w T P.salary.positive a (false,t) x F).part s
        Poly.toll P.w s * ‖(θ:ℂ) * (field (true,t)-field (false,t))‖ ≤ θ * (2 * (Coat.gStep (upper).beta)^q) := by
  obtain ⟨W,T,slots,derivatives⟩ := WilsonThermometerCompulsoryDifference.original R A simple live o hk
    D Q π Γ Ψ books ahead order shelf seats floor P way finer K₀ K₁ bound₀ bound₁ course pass training q enrolled
  have top := QuadraticLocal.Advent.later R π Γ Ψ course (floor.trans (Nat.le_succ i)) live
  have base := QuadraticLocal.Advent.later R π Γ Ψ course floor live.le
  have band : (upper).beta ∈ Shoot.band R.alloy.B.a (i+1) := by
    rw [top.beta]
    exact (R.T.sticks N per |>.prices _ (Nat.zero_le _) live).2
  obtain ⟨staff⟩ := Mentor.crew D R.rolls Q R.alloy R.kit φ books pass training
    P.op (R.alloy.B.a.S.oneStep i per).exact_size (upper).beta band live lower base.truep.point top.truep.point rfl W.clock
  have room : 2*(2+(1+(1:ℝ))) ≤ Mentor.capDay := by norm_num [Mentor.capDay]
  have width : 0 ≤ (lower).p.supportExponent+1+1 := by linarith [(lower).p.exponent_pos]
  refine ⟨W,T,slots,fun t θ nonnegative => ⟨derivatives t θ nonnegative,?_⟩⟩
  intro F s v hv
  have paid := WilsonReceivedCompulsoryRate.through (k:=P.op.count) (P':=(lower))
    W.clock staff.real (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w T P.salary.positive slots room
    (false,t) (enrolled.trans_eq staff.paid.1.symm) P.issued.Waffle.breeze.2.1
  exact WilsonReceivedCompulsoryFaces.difference W.clock (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w T P.salary.positive slots (false,t)
    paid P.voter.room width (false,t) (true,t) F s v hv θ nonnegative

end YM.Integration.WilsonThermometerCompulsoryLog
end
