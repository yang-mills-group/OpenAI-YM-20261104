import YM.Integration.WilsonReceivedCloseQCalendar
import YM.Integration.WilsonReceivedFirstQIncidence
/-! The two original incurred curvature source fees, before any subsequent finite comparison degree. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseQNamedSalary
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra
open QuadraticLocal.Rebirth ConnectedActivityE6 FullQLocal FullQLocal.RenderedStep
open Multi Exterior WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open private staff from YM.Integration.WilsonOriginalClubSourcePackets
open Source Labels LocalComparison ComparisonDensity.Address Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonMixedPassportVote
open Pert.Asymptotics Extra.Histories WilsonOriginalReceivedChain
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) (simple : G.Simple) {B : MS.Local.Physical.Deck G}
  {V : Type} [DecidableEq V] [Fintype V] [Nonempty V] (request : Request V) (freshQ : MS.Land.Prescription B)
  (u : V → MS.Rake.Label B) (μ : ℝ) (extra : V → ℕ)
  {φ : ℕ → ℕ} (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (income : WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
  (K : ℕ)
local notation "free" => (fun _ : V => (1:ℝ))
local notation "freePos" => (fun _ : V => zero_lt_one (α:=ℝ))
local notation "offer" => WilsonOriginalMixedFiniteVoter.original R request freshQ u μ extra free D income simple K 0 freePos (zero_lt_one : (0:ℝ)<1)
local notation "factor" => Classical.choose offer
local notation "exponent" => (Classical.choose_spec offer).2.choose


variable {k:ℕ} (Q : D.Tab R.rolls) (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  (way : WayStation R.kit) (ticket : TicketP R.alloy R.kit D Q)
  (warm : QuadraticLocal.Spill.Raffle.Warm G D R.alloy.delay φ)
  (education : Mentor.Educated D R.rolls Q R.kit.shape R.kit.scout φ books R.alloy.delay)
  (employment : ∀d,MintClock.Employment D φ d (R.rolls.L d))
  (calendar : MintClock.Regency D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  (pass : Pass D Q R.alloy R.kit)
  (upperJ:Request V) (upperQ:MS.Land.Prescription B) (upperLabels:V→MS.Rake.Label B)
  (upperClock:ℝ) (upperExtra:V→ℕ) (upperOrder target order shelf:ℕ)
  (upperRank:ActualOriginalQLayout.rankCap R upperLabels ≤ order) (old:Finset V)
local notation "purchased" => WilsonReceivedCalibratedUpper.prepaid R simple upperJ upperQ upperLabels upperClock
  upperExtra free D Q way ticket warm income books ahead education employment calendar hospital pass upperOrder freePos
local notation "upperBank" => (Classical.choose_spec purchased).2.choose_spec order 0 target upperRank (zero_lt_one : (0:ℝ)<1)
local notation "hQ" => ActualOriginalQLayout.rankCap R u+Fintype.card V*WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u+1
local notation "incomeQ" => WilsonOriginalFreshQAtReceivedDate.prepaid R simple request freshQ u μ extra free D income warm K freePos

def degree : ℕ := WilsonReceivedFirstQIncidence.degree ((Classical.choose_spec purchased).2.choose) exponent
  ((Classical.choose_spec incomeQ).2.choose) (QuadraticLocal.Spill.Raffle.pad hQ)

local notation "d₀" => degree R simple request freshQ u μ extra D income K Q books ahead way ticket warm
  education employment calendar hospital pass upperJ upperQ upperLabels upperClock upperExtra upperOrder

def currency : ℝ := max 1 ((WilsonReceivedFirstQIncidence.fee (Classical.choose purchased) factor
  (Classical.choose incomeQ) 1)*(8:ℝ)^d₀)

end YM.Integration.WilsonReceivedCloseQNamedSalary
