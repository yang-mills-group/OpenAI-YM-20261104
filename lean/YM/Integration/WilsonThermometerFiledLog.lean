import YM.Integration.WilsonThermometerFullLogReturn
import YM.Integration.WilsonReceivedCompulsoryFullLog
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
namespace YM.Integration.WilsonThermometerFiledLog
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
variable (observed : Wallet disks → Config G (R.family.side (i+1) per) → Poly (Stock.census (Fin 3)))
variable (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead disks sectors ages
  order shelf seats i floor observed)
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


/-- Complete signed regular logarithms at the prescribed first-join factor,
on the actual booked test purse and every older genuine Wilson posterior. -/
def Heard (K₀ K₁ : hardSlot) (θ : ℝ) (q : ℕ) : Prop :=
    ∃ (W : schedule) (T : Travel.Seal (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w 2 (1+1))
      (a : HasSlots (upper).p (upper).activities), ∀ (t : Wallet disks),
      ∀ (s : (Stock.census (Fin 3)).Mode) (v : Fin 3), v ∈ s.val →
        let field := fun (x : Bool × Wallet disks) (F : Config G (R.family.side i per)) =>
          (WilsonReceivedCompulsoryFullLog.fullLog (k:=P.op.count) (P':=(lower))
            W.clock (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w T P.salary.positive a (false,t) x F).part s
        let debt := fun F => Poly.toll P.w s • ((θ:ℂ) * (field (true,t) F-field (false,t) F))
        WilsonThermometerCompulsoryReturn.Heard R (top:=N) debt (θ*(2*(Coat.gStep (upper).beta)^q))

theorem original (authentic : observed = offered R A simple live o) (way : WayStation R.kit) (finer : i+1<N) (K₀ K₁ : hardSlot)
    (bound₀ : K₀.Paid P.w (upper).p.B (upper).p.supportExponent quote)
    (bound₁ : K₁.Paid P.w (upper).p.B (upper).p.supportExponent quote)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (pass : AllOrder.Transit.Pass D Q R.alloy R.kit)
    (training : Mentor.Educated D R.rolls Q R.kit.shape R.kit.scout φ books R.alloy.delay)
    (θ : ℝ) (hθ : 0 ≤ θ) (q : ℕ) (enrolled : q ≤ P.op.stage) :
    Heard R hk D Q π Γ Ψ books ahead order shelf seats floor observed P K₀ K₁ θ q := by
  subst observed
  obtain ⟨W,T,slots,hearing⟩ := WilsonThermometerFullLogReturn.original R A simple live o hk
    D Q π Γ Ψ books ahead order shelf seats floor P way finer K₀ K₁ bound₀ bound₁ course pass training q enrolled
  exact ⟨W,T,slots,fun t => hearing t θ hθ⟩

end YM.Integration.WilsonThermometerFiledLog
end
