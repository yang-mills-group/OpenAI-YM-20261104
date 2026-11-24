import YM.Integration.WilsonThermometerSameWalkStep
import YM.Integration.WilsonThermometerSameWalkTariff

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkRated
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
include P in
/-- Engineering-restored original Wilson null gate at every displaced source. The two actual hard carriers and all induced regular and forced outputs are retained. -/
theorem original (ticket:V) (live:i<N) (simple:G.Simple)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (scroll:VowsR.LawScroll G φ) (chamber:VowsR.Chamber scroll R.kit D Q books)
    (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (size:seats ≤ Burn.horizon k+2)
    (way:WayStation R.kit)
    (M:WilsonMeasuredRankedMenu.Menu R rank)
    (slow:∀ j,((R.family.S.block j).val:ℝ) ≤ Real.log (Lambda R.family.path.levels j))
    (prepared:WilsonReportLampForecast.Ready R.family.path.levels)
    (fixed:(R.family.path.levels.budget i).supportExponent ≤ 100)
    (q:ℕ) (deep:2*(q+4+1)+8≤order) (aged:q+4+4≤3*k+2) (accuracy:2*rank+5≤q)
    (eligible:Ready R simple rank q k order shelf M slow prepared accuracy deep aged i)
    (step : TicketP R.alloy R.kit D Q)
    (calendar:WilsonOriginalNullAppointments.Paid R rank i)
    (h : Coefficient (F₀) (R.family.side (i+1) per)) (B : ℝ)
    (form : h.Format origin Y₀ (incoming)) (fund : h.remBound origin (incoming) κ₁ B)
    (onset:M.onset ≤ i) :
    let v:=Germ.projection F₀ Y₀ (incoming).p.threshold origin h
    ∃ z:Coefficient (F₀) (R.family.side i per), z.Format coarse Y₀ (Ψ i) ∧
      z.remBound coarse (Ψ i) κ₀ (L₀^(-(1/8:ℝ))*B+WilsonThermometerSameWalkTariff.charge R rank M i*(F₀).coeffSize v) ∧
      z.density coarse S₀ (Ψ i)=GermGraph.transition (C:=R.family) rank N per i (h.density origin S₀ (incoming)):=by
  intro v
  obtain ⟨z,u,shaped,fee,hu,discount,law⟩:=WilsonThermometerSameWalkStep.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor
    physical P origin rank ticket live simple course scroll chamber pass hospital size way M slow prepared fixed q deep aged accuracy eligible step calendar h B form fund
  have columns:0≤(R.family.path.levels.params i).columns:=zero_le_one.trans (R.family.path.levels.params i).columns_ge
  have gain:u≤L₀^(-(1/8:ℝ))*B:=le_trans (by nlinarith only [columns,hu,mul_nonneg columns hu]) discount
  have point:(incoming).p=R.family.path.levels.budget (i+1):=(QuadraticLocal.Advent.later R π Γ Ψ course (floor.trans i.le_succ) live).truep.point
  refine ⟨z,shaped,rem_mono fee (add_le_add gain ?_),law⟩
  rw [point]
  simpa only [v,point] using WilsonThermometerSameWalkTariff.paid R rank M onset origin v

end YM.Integration.WilsonThermometerSameWalkRated
end
