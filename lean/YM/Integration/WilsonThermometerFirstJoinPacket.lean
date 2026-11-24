import YM.Integration.WilsonThermometerAppointedPhysical
import YM.Integration.WilsonThermometerCompulsoryExit

/-! The same original filed post carries its unweighted exceptional regular
return and the complete once-divided newly forced activity. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerFiledExit
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

theorem paid (same : observed=offered R A simple live o) (way : WayStation R.kit)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (p : ℕ) (funded : p+6*seats ≤ R.alloy.B.a.clock.J i) :
    P.output.hard.Paid P.w (Ψ i).p.B (Ψ i).p.supportExponent
      ((R.alloy.B.a.clock.hatBeta (i+1))^(-(p:ℝ))*LocalComparison.forcedDivisor R.family i) := by
  subst observed
  exact WilsonThermometerCompulsoryExit.original R A simple live o hk D Q π Γ Ψ books ahead order shelf seats floor
    P way course p funded

end YM.Integration.WilsonThermometerFiledExit
end

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerFirstJoinPacket
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity QuadraticLocal.Tint Pressure ConnectedActivityE6
open WilsonOriginalReceivedChain WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open FVA1 Finset Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter OriginalForcedAddresses
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonThermometerCourseIntake
open scoped Classical BigOperators Topology

open WilsonThermometerCourseHearing WilsonPositionThermometerGradedReading LocalComparison ActualPolynomialContraction MergeProof.Accent
open WilsonOriginalStarSceneRent WilsonOriginalThermometerTollBudget
open WilsonOriginalThermometerMicroscopic


variable {G : Gauge} (R : Run G) {m j N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  (order shelf seats : ℕ) (floor : m ≤ j) (A : Group R.family 6)
  (simple : G.Simple) (cut : j+1<N) (o : Positions (Fin 3) (R.family.side N per))
local notation "actors" => disks
local notation "pieces" => sectors
local notation "grades" => (fun z : Fin 3 => (grade z).val)

variable (P : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1)
    (floor.trans (Nat.le_succ j)) (offered R A simple cut o))

local notation "earlier" => (fun x : Wallet actors => LocalComparison.actualPush R.family N per (j+1) ((offered R A simple cut o) x))
local notation "elected" => Oak.expenseReal R hk D Q π Γ books (floor.trans (Nat.le_succ j)) P.op P.lesson ahead order shelf
local notation "hi" => floor.trans (Nat.le_succ j)
variable [Countable P.inputIndex]
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  (scroll:VowsR.LawScroll G φ) (chamber:VowsR.Chamber scroll R.kit D Q books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  (load:P.op.count≤Burn.horizon k+2) (wide:shelf≤R.alloy.B.a.clock.J (j+1)) (test:Wallet actors)
local notation "initial" op:max => op R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1)
  (floor.trans (Nat.le_succ j)) (offered R A simple cut o) P simple cut course scroll chamber hospital load wide test
local notation "issued" => initial WilsonOriginalReceivedFirstEnrollment.installed
local notation "coarsePost" => Post (N:=N) (V:=Fin 3) (X:=fun _ => ℂ) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats j floor earlier
variable {firstOrder : ℕ} {ε h C E τ : ℝ}
  (receipt : WilsonThermometerFirstJoinAppointment.Record R hk D Q π Γ Ψ books ahead order shelf seats floor
    A simple cut o P course scroll chamber hospital load wide test firstOrder ε h C E τ)
variable (funded:WilsonWindowOriginalHardRadius.Booked R.kit) (d:ℕ) (select:(Stock.census (Fin 3)).Mode→Prop)
  (v:Fin 3) (contains:∀t,select t→v∈t.val)
local notation "fine" => Ψ ((j+1)+1)
local notation "quote" => Time.quoteHard R.alloy.B.a (j+1) R.kit.book (fine).beta
local notation "delta" => (↑((Real.exp ((fine).p.supportExponent/8*d))⁻¹):ℂ)
local notation "markers" dist₀:max => WilsonOriginalReceivedFirstMarkers.terms R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1) (floor.trans (Nat.le_succ j)) (offered R A simple cut o) P simple cut course scroll chamber hospital load wide test funded d select v contains dist₀
local notation "charged" dist₀:max => WilsonOriginalReceivedFirstMarkers.width R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1) (floor.trans (Nat.le_succ j)) (offered R A simple cut o) P simple cut course scroll chamber hospital load wide test funded d select v contains dist₀
local notation "apart" => ∀t, select t→∃a∈t.val, ∃b∈t.val,
    d*(4*(fine).p.B+2)+2*(fine).p.B ≤ separation (P.passport.origin a) (P.passport.origin b)
local notation "sector" => Hard (Wallet actors) (Ψ (j+1)).p (Ψ (j+1)).activities.forced (Ψ (j+1)).activities.K
  receipt.post.passport.origin (Stock.census (Fin 3))

local instance : Countable receipt.post.inputIndex := receipt.counted


open WilsonThermometerAppointedPhysical
local notation "wallet₀" => max 1 ((1+WilsonOriginalThermometerReportedGrading.cap R j 1)*
  wallet R WilsonOriginalThermometerPalette.levels (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J ((j+1)+1))))
local notation "θ" => (Real.exp ((fine).p.supportExponent/8*d))⁻¹
local notation "g" => Coat.gStep (R.family.path.rep N per (j+1)).beta

/-- The reported field already carries the extra inverse transfer. The
returned unweighted face fee is uniform in the cutoff and period. -/
theorem original (distant : apart) (refs : ∀ t : Fin 3, R.family.ref (grade t) ≤ N)
    (way : WayStation R.kit) (pass : AllOrder.Transit.Pass D Q R.alloy R.kit)
    (training : Mentor.Educated D R.rolls Q R.kit.shape R.kit.scout φ books R.alloy.delay)
    (income : WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay) (p : ℕ)
    (late : activation R D simple income p ≤ j) (enrolled : p+156 ≤ order+1)
    (extent : reach R ≤ R.alloy.B.a.clock.J ((j+1)+1)+1)
    (ep : 0 ≤ ε) (unit : ε ≤ 1)
    (coupon : ∀ s : (Stock.census (Fin 3)).Mode, Poly.toll P.w s*(wallet₀*elected)^s.val.card=1)
    (measured : (Ψ (j+1)).beta=(R.family.path.rep N per (j+1)).beta)
    (ready : p+6*seats ≤ Burn.horizon k+2) :
    receipt.post.output.hard.Paid receipt.post.w (Ψ j).p.B (Ψ j).p.supportExponent
      ((R.alloy.B.a.clock.hatBeta (j+1))^(-(p:ℝ))*LocalComparison.forcedDivisor R.family j) ∧
    ∃ (removed raised : sector), HEq removed (markers distant).removed ∧ HEq raised (markers distant).raised ∧
      WilsonOriginalForcedMarkerMerger.Related v delta removed receipt.post.input.hard raised ∧
      WilsonThermometerRawLog.Priced R hk D Q π Γ Ψ books ahead order shelf seats floor earlier receipt.post removed raised
        θ (θ*WilsonThermometerReportedPower.price R*g^p) := by
  refine ⟨?_,?_⟩
  · exact WilsonThermometerFiledExit.paid R A simple (Nat.lt_of_succ_lt cut) o hk D Q π Γ Ψ books ahead
      order shelf seats floor earlier receipt.post (WilsonThermometerOfferedStep.original R A simple cut o refs)
      way course p (ready.trans (hk.trans (R.alloy.B.a.fits.mono floor)))
  · exact WilsonThermometerAppointedPhysical.original R hk D Q π Γ Ψ books ahead order shelf seats floor
      A simple cut o P course scroll chamber hospital load wide test receipt funded d select v contains
      distant refs way pass training income p late (enrolled.trans receipt.post.voter.height) extent P.small ep unit coupon measured

end YM.Integration.WilsonThermometerFirstJoinPacket
end
