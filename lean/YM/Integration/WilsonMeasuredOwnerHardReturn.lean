import YM.Integration.WilsonMeasuredOwnerEdge
import YM.Integration.WilsonMeasuredOwnerAbsorption

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnerHardReturn
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
open RG16 WilsonMeasuredCoefficientTransport
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
local notation "E₁" => Earn.Passport.point (fun _:Fin 1=>(0:Site (R.family.side (i+1) per)))
local notation "model₁" => (Empty.elim : Empty → Row (E₁) (labels₁) G (Wallet disk))
variable (rank:ℕ)
local notation "F₀" => R.family.labels.level rank
local notation "S₀" => R.family.localSection rank
local notation "Y₀" => R.family.params
local notation "scaleCost" => WilsonMeasuredRankedResidual.sourceCost R rank
local notation "wrap" => WilsonMeasuredRankedPrimaryBudget.wrap (F₀) Y₀


/-- The first eligible date for the stable numerical margin is fixed before
choosing either physical regulator, the real input field, or the old coefficient. -/
def opening (simple:G.Simple) (M:WilsonMeasuredRankedMenu.Menu R rank) (q:ℕ)
    (accuracy:2*rank+5≤q)
    (slow:∀i,((R.family.S.block i).val:ℝ)≤Real.log (Lambda R.family.path.levels i))
    (prepared:WilsonReportLampForecast.Ready R.family.path.levels) : ℕ :=
  (Filter.eventually_atTop.mp (WilsonMeasuredOwnerAbsorption.original R simple rank q
    (WilsonMeasuredOwnerFare.unitCost scaleCost M.cost wrap q) accuracy slow prepared)).choose

/-- The genuine hard-only branch of the physical projected descent. All incomes
and the one elected post are fixed before choosing the deposited coefficient. -/
theorem original (ticket:V) (live:i<N) (simple:G.Simple)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (scroll:VowsR.LawScroll G φ) (chamber:VowsR.Chamber scroll R.kit D Q books)
    (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (size:seats ≤ Burn.horizon k+2) (shelfFit:shelf ≤ R.alloy.B.a.clock.J i)
    (way:WayStation R.kit) (small:cash ≤ κ₁/2)
    (M:WilsonMeasuredRankedMenu.Menu R rank)
    (slow:∀ j,((R.family.S.block j).val:ℝ) ≤ Real.log (Lambda R.family.path.levels j))
    (prepared:WilsonReportLampForecast.Ready R.family.path.levels)
    (fixed:(R.family.path.levels.budget i).supportExponent ≤ 100)
    (date:R.t rank ≤ i) (active:M.onset ≤ i)
    (late:WilsonCenteredCaptureClock.first R simple ≤ i)
    (gross:WilsonReceivedSourceGross.opening R simple ≤ i)
    (fare:WilsonOlderSignedOneMarkPhysicalFare.opening R simple slow prepared ≤ i)
    (q:ℕ) (ready:q+6 ≤ R.alloy.B.a.clock.J i) (deep:2*(q+4+1)+8 ≤ order)
    (aged:q+4+4 ≤ 3*k+2)
    (earned:WilsonFirstReceivedEarnedFee.opening R simple P.op.count (q+4) order k deep aged
      (show (0:ℝ)<1 by norm_num) ≤ i)

    (accuracy:2*rank+5 ≤ q) (window:opening R rank simple M q accuracy slow prepared ≤ i)
    {spare:ℝ} (margin:0<spare) :
    ∀ (h:Coefficient (F₀) (R.family.side (i+1) per)) (B:ℝ),
      h.Format 0 Y₀ (incoming) ∧ h.remBound 0 (incoming) κ₁ B →
      ∃ (z:Coefficient (F₀) (R.family.side i per)) (u:ℝ),
        (z.Format 0 Y₀ (Ψ i) ∧ z.remBound 0 (Ψ i) κ₀ u) ∧ (F₀).coeffSize z.x ≤ u ∧
        GermGraph.transition (C:=R.family) rank N per i (account h (incoming)) = z.density 0 S₀ (Ψ i) ∧
        (2+4*(R.family.path.levels.params i).columns)*u ≤ L₀^(-(1/8:ℝ))*B + spare := by
  intro h B adm
  let C:=WilsonMeasuredOwnerFare.unitCost scaleCost M.cost wrap q
  have stage:= (Filter.eventually_atTop.mp
    (WilsonMeasuredOwnerAbsorption.original R simple rank q C accuracy slow prepared)).choose_spec i window N per live
  have bn:=Extra.Histories.rem_nonneg adm.2
  have box:0<2*(B+spare):=mul_pos (by norm_num) (add_pos_of_nonneg_of_pos bn margin)
  let w:ℝ:=(2*(B+spare))⁻¹
  have wp:0<w:=inv_pos.mpr box
  have fit:w*B ≤ 1/2:=by
    change (2*(B+spare))⁻¹*B ≤ _
    rw [inv_mul_le_iff₀ box]
    linarith
  obtain ⟨z,u,fmt,rem,primary,whole,toll⟩:=WilsonMeasuredOwnerEdge.original R hk D Q π Γ Ψ books ahead
    actors pieces grades order shelf seats floor physical P rank ticket live simple course scroll chamber pass
    hospital size shelfFit way small M slow prepared fixed date active late gross fare q ready deep aged
    earned stage.2.1 h B w adm.1 adm.2 wp fit
  refine ⟨z,u,⟨fmt,rem⟩,primary,whole,?_⟩
  have charge:u≤2*(B+spare)*(L₀^rank*(C*g₁^q)):= (inv_mul_le_iff₀ box).mp toll
  let H:ℝ:=(R.family.path.levels.params i).columns
  have hn:0≤H:=zero_le_one.trans (R.family.path.levels.params i).columns_ge
  have one:1≤L₀:=by exact_mod_cast (R.family.S.block i).pos
  have shrink:L₀^(-(1/8:ℝ))≤1:=by
    calc
      _ ≤ L₀^(0:ℝ):=Real.rpow_le_rpow_of_exponent_le one (by norm_num)
      _ = 1:=Real.rpow_zero _
  calc
    (2+4*H)*u ≤ (2+4*H)*(2*(B+spare)*(L₀^rank*(C*g₁^q))):= mul_le_mul_of_nonneg_left charge (by positivity)
    _ = ((2+4*H)*(2*L₀^rank*(C*g₁^q)))*(B+spare):=by ring
    _ ≤ L₀^(-(1/8:ℝ))*(B+spare):=mul_le_mul_of_nonneg_right stage.2.2 (add_nonneg bn margin.le)
    _ ≤ _:=by rw [mul_add];exact add_le_add le_rfl (mul_le_of_le_one_left margin.le shrink)

end YM.Integration.WilsonMeasuredOwnerHardReturn
