import YM.Integration.WilsonOriginalReceivedFirstTransfer
import YM.Integration.WilsonThermometerFiledLog
import YM.Integration.WilsonThermometerOfferedStep

/-! The joined first hard withdrawal of the authentic three-field thermometer. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerFirstJoinReturn
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


private theorem attend {K : Type*} {W : Prop} {left right paid : K → Prop} {related heard : K → K → Prop}
    (grant : W → ∃ a b, left a ∧ right b ∧ paid a ∧ paid b ∧ related a b)
    (applyReading : ∀ a b, paid a → paid b → heard a b) :
    W → ∃ a b, left a ∧ right b ∧ related a b ∧ heard a b := by
  intro wage
  obtain ⟨a,b,ha,hb,pa,pb,link⟩ := grant wage
  exact ⟨a,b,ha,hb,link,applyReading a b pa pb⟩

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
variable (L:WilsonOriginalReceivedChain.Post (N:=N) (V:=Fin 3) (X:=fun _ => ℂ) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats j floor (fun x : Wallet actors => LocalComparison.actualPush R.family N per (j+1) ((offered R A simple cut o) x))) (filed:WilsonOriginalReceivedChain.Filed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
  (j:=j) floor (offered R A simple cut o) (WilsonOriginalReceivedFirstEnrollment.installed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1) (floor.trans (Nat.le_succ j)) (offered R A simple cut o) P simple cut course scroll chamber hospital load wide test) L)
variable (h:ℝ) (full:1≤h)
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
  L.passport.origin (Stock.census (Fin 3))

variable [Countable L.inputIndex]

include filed full in
/-- The two paid programs are the literal last-merger outcomes at this
physical birth. Their complete regular log difference is heard with the
first-join spatial factor and actual test toll on each older course. -/
theorem original (distant : apart) (refs : ∀ t : Fin 3, R.family.ref (grade t) ≤ N)
    (way : WayStation R.kit) (pass : AllOrder.Transit.Pass D Q R.alloy R.kit)
    (training : Mentor.Educated D R.rolls Q R.kit.shape R.kit.scout φ books R.alloy.delay)
    (orderRead : ℕ) (enrolled : orderRead ≤ L.op.stage) :
    (∀ a : Fin 3, L.w a=P.w a/(elected^6*h)) →
    ∃ (removed raised : sector), HEq removed (markers distant).removed ∧ HEq raised (markers distant).raised ∧
      WilsonOriginalForcedMarkerMerger.Related v delta removed L.input.hard raised ∧
      WilsonThermometerFiledLog.Heard R hk D Q π Γ Ψ books ahead order shelf seats floor earlier L removed raised
        ((Real.exp ((fine).p.supportExponent/8*d))⁻¹) orderRead := by
  apply attend (WilsonOriginalReceivedFirstTransfer.joined R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      floor (offered R A simple cut o) P simple cut course scroll chamber hospital load wide test L filed h full funded d select v contains distant)
  intro removed raised paid₀ paid₁
  have identity := WilsonThermometerOfferedStep.original R A simple cut o refs
  exact WilsonThermometerFiledLog.original R A simple (Nat.lt_of_succ_lt cut) o hk D Q π Γ Ψ books ahead
    order shelf seats floor earlier L identity way cut removed raised paid₀ paid₁ course pass training
    _ (inv_nonneg.mpr (Real.exp_pos _).le) orderRead enrolled

end YM.Integration.WilsonThermometerFirstJoinReturn
end
