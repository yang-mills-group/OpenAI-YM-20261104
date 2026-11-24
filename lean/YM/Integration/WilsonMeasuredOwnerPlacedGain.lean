import YM.Integration.WilsonMeasuredOwnerAppointments
import YM.Integration.WilsonMeasuredOwnerZero
import YM.Integration.WilsonMeasuredOwnerPlacedEdge

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnerPlacedGain
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



/-- The extra factor is purchased before both regulators and all physical sources. -/
theorem small (simple:G.Simple) (q:ℕ) (C ε:ℝ) (pos:0<ε) (accuracy:2*rank+5≤q)
    (slow:∀ j,((R.family.S.block j).val:ℝ) ≤ Real.log (Lambda R.family.path.levels j))
    (prepared:WilsonReportLampForecast.Ready R.family.path.levels) :
    ∀ᶠ i:ℕ in Filter.atTop, ∀ N per,i<N →
      let g:=Coat.gStep (R.family.path.rep N per (i+1)).beta
      let L:ℝ:=(R.family.S.block i).val
      (2+4*(R.family.path.levels.params i).columns)*(2*L^rank*(C*g^q))≤ε*L^(-(1/8:ℝ)) := by
  filter_upwards [WilsonMeasuredOwnerAbsorption.original R simple rank q (C/ε) accuracy slow prepared]
    with i gate
  intro N per live g L
  calc
    _=ε*((2+4*(R.family.path.levels.params i).columns)*(2*L^rank*((C/ε)*g^q))):=by field_simp
    _≤_:=mul_le_mul_of_nonneg_left (gate N per live).2.2 pos.le

include P in
/-- The exact stable physical hard-return estimate without an additive invoice,
including zero-cost hard input. The arbitrary tiny analytic intake rent and the
full-marker incidence cost are restored at their actual post. -/
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
      (2*L₀^rank*((WilsonMeasuredOwnerFare.unitCost scaleCost M.cost wrap q)*g₁^q)) ≤
      ε*L₀^(-(1/8:ℝ)))
    :
    ∀ (h:Coefficient (F₀) (R.family.side (i+1) per)) (B:ℝ),
      h.Format origin Y₀ (incoming) ∧ h.remBound origin (incoming) κ₁ B →
      ∃ (z:Coefficient (F₀) (R.family.side i per)) (u:ℝ),
        (z.Format coarse Y₀ (Ψ i) ∧ z.remBound coarse (Ψ i) κ₀ u) ∧ (F₀).coeffSize z.x ≤ u ∧
        GermGraph.transition (C:=R.family) rank N per i (account h (incoming)) = z.density coarse S₀ (Ψ i) ∧
        (2+4*(R.family.path.levels.params i).columns)*u ≤ (ε*L₀^(-(1/8:ℝ)))*B := by
  intro h B data
  have Bn:=Extra.Histories.rem_nonneg data.2
  by_cases bp:0<B
  · let C:=WilsonMeasuredOwnerFare.unitCost scaleCost M.cost wrap q
    have stage:=(Filter.eventually_atTop.mp
      (WilsonMeasuredOwnerAbsorption.original R simple rank q C accuracy slow prepared)).choose_spec i
      eligible.absorption N per live
    let w:ℝ:=(2*B)⁻¹
    have owed:0<2*B:=by positivity
    have wp:0<w:=inv_pos.mpr owed
    have fit:w*B≤1/2:=by change (2*B)⁻¹*B ≤ _; rw [inv_mul_le_iff₀ owed]; linarith
    obtain ⟨z,u,fmt,rem,primary,full,income⟩:=WilsonMeasuredOwnerPlacedEdge.original R hk D Q π Γ Ψ books ahead
      actors pieces grades order shelf seats floor physical P origin rank ticket live simple course scroll chamber pass
      hospital size eligible.shelf_fit way eligible.room M slow prepared fixed eligible.rank_bought eligible.menu
      eligible.capture eligible.stock eligible.fare q eligible.height deep aged
      (eligible.earning P.op.count (P.capacity.trans_le size)) stage.2.1 h B w data.1 data.2 wp fit
    refine ⟨z,u,⟨fmt,rem⟩,primary,full,?_⟩
    have charged:u≤2*B*(L₀^rank*(C*g₁^q)):= (inv_mul_le_iff₀ owed).mp income
    let H:ℝ:=(R.family.path.levels.params i).columns
    have Hn:0≤H:=zero_le_one.trans (R.family.path.levels.params i).columns_ge
    calc
      (2+4*H)*u≤(2+4*H)*(2*B*(L₀^rank*(C*g₁^q))):=mul_le_mul_of_nonneg_left charged (by positivity)
      _=((2+4*H)*(2*L₀^rank*(C*g₁^q)))*B:=by ring
      _≤_:=mul_le_mul_of_nonneg_right
        extra bp.le
  · have bz:B=0:=le_antisymm (not_lt.mp bp) Bn
    subst B
    let C:=WilsonMeasuredOwnerFare.unitCost scaleCost M.cost wrap q
    have stage:=(Filter.eventually_atTop.mp
      (WilsonMeasuredOwnerAbsorption.original R simple rank q C accuracy slow prepared)).choose_spec i
      eligible.absorption N per live
    obtain ⟨z,u,format,bill,_,_,_⟩:=WilsonMeasuredOwnerPlacedEdge.original R hk D Q π Γ Ψ books ahead
      actors pieces grades order shelf seats floor physical P origin rank ticket live simple course scroll chamber pass
      hospital size eligible.shelf_fit way eligible.room M slow prepared fixed eligible.rank_bought eligible.menu
      eligible.capture eligible.stock eligible.fare q eligible.height deep aged
      (eligible.earning P.op.count (P.capacity.trans_le size)) stage.2.1 h 0 1 data.1 data.2 zero_lt_one (by norm_num)
    refine ⟨stretch (0:ℂ) z,0,⟨stretch_format _ format,by simpa using stretch_rem (0:ℂ) bill⟩,?_,?_,by simp⟩
    · change (F₀).coeffSize ((0:ℂ) • z.x)≤0
      rw [Size.smul,norm_zero,zero_mul]
    · rw [WilsonMeasuredOwnerZero.field data.2]
      funext U
      simp [GermGraph.transition,Extra.Histories.blast,RG.StepData.push,stretch_density]

end YM.Integration.WilsonMeasuredOwnerPlacedGain
