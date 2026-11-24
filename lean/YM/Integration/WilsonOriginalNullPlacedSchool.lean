import YM.Integration.WilsonOriginalNullPlacedParallel
import YM.Integration.WilsonOriginalNullParallel
import YM.Integration.WilsonOriginalNullJointLanding
import YM.Integration.WilsonOriginalNullBooked

/-! Emit the actual measured lower primary and a projection-null lower source
on the very same original Wilson history. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedSchool
open YM.Integration.WilsonMeasuredOwnerReserve
open Labels Source WilsonPhysicalMarkedDefect.RegularProjection
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
variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)


variable (floor : m ≤ i)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i floor physical)
open Pert.Asymptotics Extra.Histories Trace.Physical.GermGraph Trace.Physical
open RG16 WilsonMeasuredCoefficientTransport WilsonMeasuredOwnerAppointments
open Progress.DirectedRecipe QuadraticLocal.Tint

local notation "incoming" => Ψ (i+1)
local notation "κ₁" => LocalComparison.forcedDivisor R.family (i+1)
local notation "κ₀" => LocalComparison.forcedDivisor R.family i
local notation "cash" => R.family.path.levels.clock.forcedAllowance (i+1)
local notation "labels₁" => Stock.census (Fin 1)
local notation "temperature" => R.alloy.B.a.clock.hatBeta (i+1)

local notation "hc" => R.family.path.rep N per (i+1)
local notation "g₁" => Coat.gStep (hc).beta
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books floor P.op P.lesson ahead order shelf
local notation "L₀" => ((R.family.S.block i).val:ℝ)
variable (origin:Site (R.family.side (i+1) per))
local notation "coarse" => (R.family.path.levels.clock.op i per).ratio.parent origin
variable (rank:ℕ)
local notation "F₀" => R.family.labels.level rank
local notation "S₀" => R.family.localSection rank
local notation "Y₀" => R.family.params
local notation "scaleCost" => WilsonMeasuredRankedResidual.sourceCost R rank
local notation "wrap" => WilsonMeasuredRankedPrimaryBudget.wrap (F₀) Y₀



open Extra.Histories Extra.Histories.Relay Next.Foundations
open WilsonPhysicalMarkedDefect.RegularProjection

/-- The original school elects one date gate before both physical regulators
and all incoming marked sources. Each additional branch is later heard on
one of the same two Wilson carriers. -/
theorem appointments (rank q:ℕ) {ε:ℝ} (ep:0<ε) (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (M:WilsonMeasuredRankedMenu.Menu R rank)
    (slow:WilsonWindowReportingPace.Slow R.kit) (prepared:WilsonReportLampForecast.Ready R.family.path.levels)
    (roster:∀ j,j ≤ (R.metals.p.profile j).order ∧ j ≤ (R.metals.p.profile j).power)
    (accuracy:2*rank+5≤q) (deep:2*(q+4+1)+8≤order) (aged:q+4+4≤3*k+2) :
    ∀ᶠ i:ℕ in atTop,
      WilsonOriginalNullBooked.Date R rank simple M q ε i ∧
      Ready R simple rank q k order shelf M slow.2 prepared accuracy deep aged i ∧
      (∀ p,Opened R.family rank i p) ∧
      ∀ N p, i<N → ∀ W:(∀ j,Rep G (R.family.side j p)), ∀ y:Site (R.family.side (i+1) p),
        (∃ a b c t j:ℝ,(W (i+1)).Lawful a b c t j) →
        WilsonOriginalNullPlacedStep.Coupled R.family rank N p i W y ε →
        WilsonOriginalNullPlacedParallel.Joined R.family rank N p i W y ε := by
  filter_upwards [WilsonOriginalNullBooked.original R rank simple M q ep accuracy slow prepared roster,
    WilsonMeasuredOwnerAppointments.original R simple rank q k order shelf M slow.2 prepared accuracy deep aged,
    open_late R.family simple rank,WilsonOriginalNullPlacedParallel.original rank R simple shop ep] with m a b c t
  exact ⟨a,b,c,t⟩

include P in
theorem original (ticket:V) (live:i<N) (simple:G.Simple)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (scroll:VowsR.LawScroll G φ) (chamber:VowsR.Chamber scroll R.kit D Q books)
    (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (size:seats ≤ Burn.horizon k+2)
    (way:WayStation R.kit)
    (M:WilsonMeasuredRankedMenu.Menu R rank)
    (slow:WilsonWindowReportingPace.Slow R.kit)
    (prepared:WilsonReportLampForecast.Ready R.family.path.levels)
    (fixed:(R.family.path.levels.budget i).supportExponent ≤ 100)
    (q:ℕ) (deep:2*(q+4+1)+8≤order) (aged:q+4+4≤3*k+2) (accuracy:2*rank+5≤q)
    (step:TicketP R.alloy R.kit D Q)

    (shop:RG05Preconstruction.ReadoutPurchase R.b) {ε:ℝ} (ep:0<ε)
    (roster:∀ j,j ≤ (R.metals.p.profile j).order ∧ j ≤ (R.metals.p.profile j).power)
    (date:(eventually_atTop.mp (appointments R (k:=k) order shelf rank q ep simple
      shop M slow prepared roster accuracy deep aged)).choose ≤ i) :
    WilsonOriginalNullPlacedParallel.Joined R.family rank N per i Ψ origin ε := by
  obtain ⟨calendar,eligible,home,push⟩:=(eventually_atTop.mp (appointments R (k:=k) order shelf rank q ep simple
    shop M slow prepared roster accuracy deep aged)).choose_spec i date
  have upper:=QuadraticLocal.Advent.later R π Γ Ψ course (Nat.le_succ_of_le floor) live
  exact push N per live Ψ origin ⟨_,_,_,_,_,upper.truep.valid⟩
    (WilsonOriginalNullPlacedStep.original R hk D Q π Γ Ψ books ahead actors pieces grades
      order shelf seats floor physical P origin rank ticket live simple course scroll chamber pass hospital size way M
      slow.2 prepared fixed q deep aged accuracy eligible step (home per) ε ep calendar)

end YM.Integration.WilsonOriginalNullPlacedSchool
