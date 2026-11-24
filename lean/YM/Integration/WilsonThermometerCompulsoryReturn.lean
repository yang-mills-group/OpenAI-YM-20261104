import YM.Integration.WilsonThermometerCompulsoryLog
import YM.Integration.WilsonReceivedCompulsoryMeasurable
import YM.Integration.ActualWilsonAbsoluteTransport
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
namespace YM.Integration.WilsonThermometerCompulsoryReturn
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
open Progress.DirectedRecipe QuadraticLocal.Tint OPE.Therm

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


/-- A signed contribution on the true older conditional, with every integrable
spectator on that older field kept inside the same expectation. -/
def Heard {j p top : ℕ} (f : Config G (R.family.side j p) → ℂ) (cap : ℝ) : Prop :=
  ∀ (u : ℕ) (h : u ≤ j),
    let heard := actualTransport R.family (N:=top) f h
    let μ := scene R.family.path top p u
    (∀ F, ‖heard F‖ ≤ cap) ∧ ∀ (Y : Config G (R.family.side u p) → ℂ), Integrable Y μ →
      Integrable (fun F => Y F * heard F) μ ∧
      ‖∫ F,Y F * heard F ∂μ‖ ≤ (∫ F, ‖Y F‖ ∂μ) * cap

private theorem earlier {j p top : ℕ} (atDate : j ≤ top)
    {f : Config G (R.family.side j p) → ℂ} {cap : ℝ}
    (borel : Measurable f) (bound : ∀ F, ‖f F‖ ≤ cap) : Heard R (top:=top) f cap := by
  intro u h
  have initial := ActualWilsonAbsoluteTransport.weighted R.family R.makes atDate (show RG.Envelope f from ⟨borel,cap,bound⟩)
  have older := actualScene_integrable_of_weighted R.family R.makes (h.trans atDate)
    (actualTransport_weighted_integrable_of_integrable R.family R.makes atDate initial h)
  have raw := actualTransport_norm_le R.family R.makes atDate bound h
  refine ⟨raw,fun Y hY => ?_⟩
  have bounded := (hY.norm.mul_const cap)
  have point : ∀ᵐ F ∂scene R.family.path top p u,
       ‖Y F * actualTransport R.family (N:=top) f h F‖ ≤ ‖Y F‖ * cap := by
    apply ae_of_all
    intro F
    exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_left (raw F) (norm_nonneg _))
  exact ⟨bounded.mono' (hY.aestronglyMeasurable.mul older.aestronglyMeasurable) point,
    (norm_integral_le_of_norm_le bounded point).trans_eq (integral_mul_const _ _)⟩

theorem original (way : WayStation R.kit) (finer : i+1<N) (K₀ K₁ : hardSlot)
    (bound₀ : K₀.Paid P.w (upper).p.B (upper).p.supportExponent quote)
    (bound₁ : K₁.Paid P.w (upper).p.B (upper).p.supportExponent quote)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (pass : AllOrder.Transit.Pass D Q R.alloy R.kit)
    (training : Mentor.Educated D R.rolls Q R.kit.shape R.kit.scout φ books R.alloy.delay)
    (q : ℕ) (enrolled : q ≤ P.op.stage) :
    ∃ (W : schedule) (T : Travel.Seal (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w 2 (1+1))
      (a : HasSlots (upper).p (upper).activities), ∀ (t : Wallet disks) (θ : ℝ), 0 ≤ θ →
      ∀ (s : (Stock.census (Fin 3)).Mode) (v : Fin 3), v ∈ s.val →
        let field := fun (x : Bool × Wallet disks) (F : Config G (R.family.side i per)) =>
          (WilsonReceivedCompulsoryFaces.markedLog (k:=P.op.count) (P':=(lower))
            W.clock (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w T P.salary.positive a (false,t) x F).part s
        let debt := fun F => Poly.toll P.w s • ((θ:ℂ) * (field (true,t) F-field (false,t) F))
        Heard R (top:=N) debt (θ*(2*(Coat.gStep (upper).beta)^q)) := by
  obtain ⟨W,T,slots,issued⟩ := WilsonThermometerCompulsoryLog.original R A simple live o hk
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
  refine ⟨W,T,slots,fun t θ hθ s v hv => ?_⟩
  have paid := WilsonReceivedCompulsoryRate.through (k:=P.op.count) (P':=(lower))
    W.clock staff.real (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w T P.salary.positive slots room
    (false,t) (enrolled.trans_eq staff.paid.1.symm) P.issued.Waffle.breeze.2.1
  have measured := WilsonReceivedCompulsoryMeasurable.original W.clock (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w T P.salary.positive slots (false,t)
    paid P.voter.room width
  apply earlier R live.le
  · exact (measurable_const (a:=Poly.toll P.w s)).smul ((measurable_const (a:=(θ:ℂ))).mul ((measured (true,t) s v hv).sub (measured (false,t) s v hv)))
  · intro F
    rw [norm_smul,Real.norm_of_nonneg (Poly.worth P.salary.positive s).le]
    exact (issued t θ hθ).2 F s v hv

end YM.Integration.WilsonThermometerCompulsoryReturn
end
