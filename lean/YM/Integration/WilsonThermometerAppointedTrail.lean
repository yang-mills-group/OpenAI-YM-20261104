import YM.Integration.WilsonThermometerFirstJoinAppointment
import YM.Integration.WilsonOriginalCoveredHearing

/-! The independently printed upper bank and the appointed physical post
belong to one original filed history. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerAppointedTrail
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
local notation "gf" => Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta
local notation "B" => Advent.budgetR R

private theorem fee (Ω h b d e : ℝ) (wage : 1≤Ω) (cap : Ω≤d) (floor : 2≤b)
    (rich : 1≤d) (small : e≤2) (quote : h ≤ max 1 (max (b*d) e)) :
    Ω^6*h ≤ b^2*d^7 := by
  have b₁ : 1≤b := (by norm_num : (1:ℝ)≤2).trans floor
  have b₀ : 0≤b := zero_le_one.trans b₁
  have d₀ : 0≤d := zero_le_one.trans rich
  have enough : b ≤ b*d := le_mul_of_one_le_right b₀ rich
  have priced : h≤b*d := quote.trans (max_le (b₁.trans enough) (max_le le_rfl (small.trans (floor.trans enough))))
  have budget : Ω^6≤d^6 := pow_le_pow_left₀ (zero_le_one.trans wage) cap _
  calc
    _ ≤ Ω^6*(b*d) := mul_le_mul_of_nonneg_left priced (pow_nonneg (zero_le_one.trans wage) _)
    _ ≤ d^6*(b*d) := mul_le_mul_of_nonneg_right budget (mul_nonneg b₀ d₀)
    _ = b*d^7 := by ring
    _ ≤ b^2*d^7 := mul_le_mul_of_nonneg_right (by simpa only [pow_two] using (le_mul_of_one_le_right b₀ b₁)) (pow_nonneg d₀ _)

theorem original (small : P.rent+ε*gf^firstOrder ≤ 2) :
    WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      (floor.trans (Nat.le_succ j)) (offered R A simple cut o) (issued) j floor earlier receipt.post := by
  have strong : 2 ≤ B j := (by norm_num : (2:ℝ)≤4).trans
    (receipt.post.issued.Waffle.strong.trans receipt.post.issued.Beamwork)
  have rich : 1 ≤ B (j+1) := P.issued.Waffle.cool.trans P.issued.Beamwork
  exact WilsonReceivedCloseHistory.Trail.step WilsonReceivedCloseHistory.Trail.start receipt.filed
    (elected^6*h) (one_le_mul_of_one_le_of_one_le (one_le_pow₀ P.issued.Waffle.cool) receipt.full)
    (fee elected h (B j) (B (j+1)) _ P.issued.Waffle.cool P.issued.Beamwork strong rich small receipt.budget)
    receipt.weights

end YM.Integration.WilsonThermometerAppointedTrail
end
