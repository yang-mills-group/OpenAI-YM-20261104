import YM.Integration.WilsonMeasuredOwnerHardReturn

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnerAppointments
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

open Pert.Asymptotics Next.Foundations Extra.Histories RG16
section Prices
variable {G:Gauge} (R:Run G) (simple:G.Simple) (rank q k order shelf:ℕ)
  (M:WilsonMeasuredRankedMenu.Menu R rank)
  (slow:∀i,((R.family.S.block i).val:ℝ)≤Real.log (Lambda R.family.path.levels i))
  (prepared:WilsonReportLampForecast.Ready R.family.path.levels)
  (accuracy:2*rank+5≤q) (deep:2*(q+4+1)+8≤order) (aged:q+4+4≤3*k+2)

structure Ready (i:ℕ) : Prop where
  room : R.family.path.levels.clock.forcedAllowance (i+1) ≤ LocalComparison.forcedDivisor R.family (i+1)/2
  rank_bought : R.t rank≤ i
  menu : M.onset≤ i
  capture : WilsonCenteredCaptureClock.first R simple≤ i
  stock : WilsonReceivedSourceGross.opening R simple≤ i
  fare : WilsonOlderSignedOneMarkPhysicalFare.opening R simple slow prepared≤ i
  shelf_fit : shelf≤R.alloy.B.a.clock.J i
  height : q+6≤R.alloy.B.a.clock.J i
  earning (slots:ℕ) (load:slots≤Burn.horizon k+2) :
    WilsonFirstReceivedEarnedFee.opening R simple slots (q+4) order k deep aged
      (show (0:ℝ)<1 by norm_num) ≤ i
  absorption : WilsonMeasuredOwnerHardReturn.opening R rank simple M q accuracy slow prepared≤ i

/-- One threshold for the entire eligible interval, all enrolled programme
sizes, both regulators, and every upper hard input. -/
theorem original : ∀ᶠ i:ℕ in Filter.atTop,
    Ready R simple rank q k order shelf M slow prepared accuracy deep aged i := by
  classical
  let start:=fun s=>WilsonFirstReceivedEarnedFee.opening R simple s (q+4) order k deep aged
    (show (0:ℝ)<1 by norm_num)
  let sizes:=Finset.range (Burn.horizon k+3)
  obtain ⟨first,room⟩:=Filter.eventually_atTop.mp (WilsonMeasuredOwnerReserve.room R simple)
  filter_upwards [Filter.eventually_ge_atTop first,Filter.eventually_ge_atTop (R.t rank),
    Filter.eventually_ge_atTop M.onset,Filter.eventually_ge_atTop (WilsonCenteredCaptureClock.first R simple),
    Filter.eventually_ge_atTop (WilsonReceivedSourceGross.opening R simple),
    Filter.eventually_ge_atTop (WilsonOlderSignedOneMarkPhysicalFare.opening R simple slow prepared),
    R.alloy.B.a.fits.deep.eventually_ge_atTop (max shelf (q+6)),
    Filter.eventually_ge_atTop (sizes.sup start),
    Filter.eventually_ge_atTop (WilsonMeasuredOwnerHardReturn.opening R rank simple M q accuracy slow prepared)] with i hr r m c s f j funds abs
  refine ⟨room (i+1) (hr.trans i.le_succ),r,m,c,s,f,(le_max_left ..).trans j,
    (le_max_right ..).trans j,?_,abs⟩
  intro n load
  exact (Finset.le_sup (f:=start) (Finset.mem_range.mpr (show n<Burn.horizon k+3 by omega))).trans funds

end Prices
section Course
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



include P in
/-- The actual post of the common physical course suffices, with all its quantitative
appointments bought before the regulators by the preceding theorem. -/
theorem on_course (ticket:V) (live:i<N) (simple:G.Simple)
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
    {spare:ℝ} (margin:0<spare) :
    ∀ (h:Coefficient (F₀) (R.family.side (i+1) per)) (B:ℝ),
      h.Format 0 Y₀ (incoming) ∧ h.remBound 0 (incoming) κ₁ B →
      ∃ (z:Coefficient (F₀) (R.family.side i per)) (u:ℝ),
        (z.Format 0 Y₀ (Ψ i) ∧ z.remBound 0 (Ψ i) κ₀ u) ∧ (F₀).coeffSize z.x ≤ u ∧
        GermGraph.transition (C:=R.family) rank N per i (account h (incoming)) = z.density 0 S₀ (Ψ i) ∧
        (2+4*(R.family.path.levels.params i).columns)*u ≤ L₀^(-(1/8:ℝ))*B + spare := by
  exact WilsonMeasuredOwnerHardReturn.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
    floor physical P rank ticket live simple course scroll chamber pass hospital size eligible.shelf_fit way
    eligible.room M slow prepared fixed eligible.rank_bought eligible.menu eligible.capture eligible.stock
    eligible.fare q eligible.height deep aged (eligible.earning P.op.count (P.capacity.trans_le size))
    accuracy eligible.absorption margin

end Course
end YM.Integration.WilsonMeasuredOwnerAppointments
