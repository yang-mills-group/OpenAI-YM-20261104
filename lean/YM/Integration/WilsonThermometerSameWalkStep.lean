import YM.Integration.WilsonOriginalNullOriginalGate
import YM.Integration.WilsonThermometerSameWalkPositive

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkStep
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
    :
    let v:=Germ.projection F₀ Y₀ (incoming).p.threshold origin h
    let b:=R.family.path.levels.budget i
    let ρ:=Push.Local.factor Y₀ S₀ b.supportExponent (Next.Foundations.price G (max b.order b.power))
    let price:=Next.Foundations.price G (max (incoming).p.order (incoming).p.power)
    let forcing:=L₀^rank*(4*ρ+1)*(incoming).p.mass ((S₀).footprint origin) (price*(F₀).coeffSize ((F₀).core v))
    ∃ (z:Coefficient (F₀) (R.family.side i per)) (u:ℝ), z.Format coarse Y₀ (Ψ i) ∧
      z.remBound coarse (Ψ i) κ₀ (u+forcing) ∧ 0≤u ∧ (2+4*(R.family.path.levels.params i).columns)*u≤L₀^(-(1/8:ℝ))*B ∧
      z.density coarse S₀ (Ψ i)=GermGraph.transition (C:=R.family) rank N per i (h.density origin S₀ (incoming)):=by
  classical
  intro v b ρ price forcing
  let z0:=WilsonThermometerSameWalkSplit.remove h v
  let g0:=primary origin v
  obtain ⟨fit0,paid0,zero0,part⟩:=WilsonThermometerSameWalkSplit.measured Y₀ S₀ (incoming) origin h form fund
  obtain ⟨A,r,shapeA,paidA,_,hr,lawA⟩:=
    WilsonOriginalNullOriginalGate.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor
      physical P origin rank ticket live simple course scroll chamber pass hospital size way M slow prepared
      fixed q deep aged accuracy eligible step calendar z0 B fit0 paid0 zero0
  obtain ⟨D0,shapeD,paidD,lawD⟩:=WilsonThermometerSameWalkPositive.original R π Γ Ψ course floor live simple way D Q step (Stock.census Unit) calendar.lower calendar.upper origin v
  have setD:D0.remBound coarse (Ψ i) κ₀ forcing:=by
    have hb:R.family.S.block i=R.rolls.L (R.alloy.B.a.clock.J (i+1)):=PriceCompiler.block_eq R.alloy.B.valid i
    dsimp only [forcing];rw [hb];exact paidD
  obtain ⟨enrolled,fee⟩:=presentation shapeA paidA shapeD setD
  refine ⟨beside A D0,r,enrolled,fee,rem_nonneg paidA,hr,?_⟩
  let H:=QuadraticLocal.Advent.later R π Γ Ψ course (floor.trans i.le_succ) live
  let K:=QuadraticLocal.Advent.later R π Γ Ψ course floor live.le
  have money:g0.remBound origin (incoming) κ₁ 0:=primary_rem _ (Real.sqrt_pos.mpr (Real.exp_pos _))
  have fitted:g0.Format origin Y₀ (incoming):=primary_format _
  have ha:Integrable (z0.density origin S₀ (incoming)) (prior G _):=
    (z0.envelope S₀ H.truep.valid paid0 fit0).integrableC _
  have hd:Integrable (g0.density origin S₀ (incoming)) (prior G _):=
    (g0.envelope S₀ H.truep.valid money fitted).integrableC _
  have val:h.density origin S₀ (incoming)=z0.density origin S₀ (incoming)+g0.density origin S₀ (incoming):=funext part
  have received:D0.density coarse S₀ (Ψ i)=GermGraph.transition (C:=R.family) rank N per i (g0.density origin S₀ (incoming)):=lawD
  rw [val,transition_add rank N per ha hd,←lawA,←received]
  exact plus K.truep.valid paidA setD S₀

end YM.Integration.WilsonThermometerSameWalkStep
end
