import YM.Extra.SOURCE_HISTORIES.Beside
import YM.Integration.WilsonMeasuredOwnerPlacedReturn
import YM.Integration.WilsonOriginalNullInventory
import YM.Integration.WilsonMeasuredOnlyHard
import YM.Integration.WilsonOriginalNullStock

import YM.Integration.WilsonOriginalNullSignedAccounts
import YM.Integration.WilsonOriginalNullGain
import YM.Integration.WilsonMeasuredOwnerPlacedGain

/-! Restore regular and hard income with any fixed reserve at exponent 1/8. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullSmallAccounts
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
/-- Reclose the whole nonprimary component before it is paired with any other mark. -/
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
    (ε:ℝ)
    (extra:(2+4*(R.family.path.levels.params i).columns)*
      (2*L₀^rank*((WilsonMeasuredOwnerFare.unitCost scaleCost M.cost wrap q)*g₁^q)) ≤ ε*L₀^(-(1/8:ℝ)))
    (step : TicketP R.alloy R.kit D Q)
    (clock : WilsonOriginalNullContraction.Ready R i rank)
    (reserve : 4*(2+4*(R.family.path.levels.params i).columns)*L₀^(-(2/5:ℝ)) ≤ ε*L₀^(-(1/8:ℝ)))
    (h : Coefficient (F₀) (R.family.side (i+1) per)) (B : ℝ)
    (form : h.Format origin Y₀ (incoming)) (fund : h.remBound origin (incoming) κ₁ B) :
    ∃ (a c : ℝ) (z : Coefficient (F₀) (R.family.side i per)) (u : ℝ),
      0≤a ∧ 0≤c ∧ a+c≤B ∧ (soft h).remBound origin (incoming) κ₁ a ∧
      z.Format coarse Y₀ (Ψ i) ∧ z.remBound coarse (Ψ i) κ₀ u ∧ (F₀).coeffSize z.x ≤ u ∧
      (2+4*(R.family.path.levels.params i).columns)*u ≤ (ε*L₀^(-(1/8:ℝ)))*(a/4+c) ∧
      ∀ W, z.density coarse S₀ (Ψ i) W =
      ((R.family.S.block i).val:ℂ)^rank * (R.family.path.levels.clock.op i per).push (incoming).beta
        (fun V => ((incoming).eval V : ℂ) * ∑'j,h.maskedTerm (incoming) j V) W +
      (GermGraph.transition (C:=R.family) rank N per i (account h (incoming))) W := by
  classical
  obtain ⟨a,c,fees,ha,hcStart,total,regs,shape,cold_form,cold_income,_⟩ :=
    WilsonOriginalNullInventory.original (incoming) Y₀ origin h form κ₁ B fund
  obtain ⟨Y,fmt,old,low,Yread⟩ := WilsonOriginalNullFamily.original R π Γ Ψ course floor live origin
    simple way D Q step (Stock.census Unit) clock h.support h.regular fees a regs
    (fun j => (shape j).1) (fun j => (shape j).2)
  obtain ⟨H,v,⟨hH,hv⟩,hsize,Hread,hard⟩ :=
    WilsonMeasuredOwnerPlacedGain.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      floor physical P origin rank ticket live simple course scroll chamber pass hospital size way M slow prepared
      fixed q deep aged accuracy eligible ε extra (WilsonOriginalNullInventory.cold origin h) c ⟨cold_form,cold_income⟩
  have bl : R.family.S.block i = R.rolls.L (R.alloy.B.a.clock.J (i+1)) := block_eq R.alloy.B.valid i
  rw [←bl] at old low Yread
  let charge := L₀^(-(2/5:ℝ))*a
  have price : 0 ≤ charge := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) ha
  have hv0 : 0≤v := rem_nonneg hv
  have hcol : 0 ≤ 2+4*(R.family.path.levels.params i).columns := by
    linarith [(R.family.path.levels.params i).columns_ge]
  obtain ⟨format,budget⟩ := presentation fmt old hH hv
  have soft_paid := WilsonOriginalNullSignedAccounts.regular_wallet (κ:=κ₁) (incoming) origin h (Real.sqrt_pos.mpr (Real.exp_pos _)) ha fees regs
    (fun j=>(shape j).2)
  refine ⟨a,c,beside Y H,charge+v,ha,hcStart,total,soft_paid,format,budget,?_,?_,?_⟩
  · rw [reckon]
    refine (Size.add _ _ _).trans ?_
    have lower : (F₀).coeffSize Y.x ≤ charge := low.trans (by change charge/3 ≤ charge; linarith only [price])
    exact add_le_add lower hsize
  · unfold charge
    linarith only [mul_le_mul_of_nonneg_right reserve ha,hard]
  intro W
  have lowerLaw := (QuadraticLocal.Advent.later R π Γ Ψ course floor live.le).truep.valid
  have add := congrFun (plus lowerLaw old hv S₀) W
  refine add.trans ?_
  change Y.density coarse S₀ (Ψ i) W + H.density coarse S₀ (Ψ i) W = _
  congr 1
  · exact Yread W
  · exact (congrFun Hread W).symm

end YM.Integration.WilsonOriginalNullSmallAccounts
