import YM.Integration.WilsonReceivedCloseCoveredWalletDates
import YM.Integration.WilsonReceivedGeometricFieldPrice

/-! One reporting floor for each admissible number of occupied seats before the two regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedGeometricPriorDates
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Ac OPE.Therm WilsonLimitConstruction RG16 MSbar.Heath Labels Source Pert.Asymptotics
open WilsonRootedKioskOccupiedSlip WilsonRegisteredAffineHalo WilsonRegisteredAxialRates
open WilsonReportingForestAngularFare
open scoped Classical BigOperators Topology

open MeasureTheory Exterior ConnectedActivityE6.SliceRows

variable {G:Gauge} (R:Run G) (simple:G.Simple) {η:ℝ} {T:Campaign R} {W:Campaign.Pillars R T}
  (funded:FundedOriginalProperties.{u} simple η W)
  (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
  (J:Voice G) (clear:Clear G J)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) {φ:ℕ→ℕ}
  (width:∀j k:ℕ,k≤j→∀b:ℝ,R.alloy.delay.betaEntry j≤b→Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) j)⁻¹^2)≤b)
  (grades:Fin 3→ℕ) (order shelf k:ℕ)
  (gate:WilsonReportingForestAngularReflection.posted R) (q p loss:ℕ) (C:ℝ) {ε:ℝ} (ep:0<ε)
  (ready:WilsonReportLampForecast.Ready R.family.path.levels) (deep:2*(q+1)+8≤order) (aged:q+4≤3*k+2)

local notation "localOpen" seats:max => WilsonFirstReceivedEarnedFee.opening R simple seats q order k deep aged ep
local notation "chart" seats:max m₀:max => WilsonReceivedCloseCoveredWalletDates.Ready R simple funded slow J clear D width grades
  order shelf seats k gate q p loss C ep m₀
local notation "early" => (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose
local notation "late" => (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose
local notation "saved" => (eventually_atTop.mp (WilsonFullFaceSignedReserved.original R simple q)).choose

/-- All three genuine counters are read on that run before the positions and both cutoffs. -/
def Ready (m:ℕ) : Prop := ∀ (i : ℕ), m ≤ i → WilsonCenteredCaptureClock.first R simple ≤ i ∧ R.t 0 ≤ i ∧
  early ≤ i ∧ late ≤ i ∧ shelf ≤ R.alloy.B.a.clock.J i ∧ k ≤ R.alloy.B.a.clock.J i ∧ q ≤ R.alloy.B.a.clock.J i ∧
  saved ≤ i ∧ ∀ (seats : ℕ),seats ≤ Burn.horizon k+2 → localOpen seats  ≤ i ∧ chart seats i

set_option linter.flexible false in
theorem scheduled : ∀ᶠ m : ℕ in atTop,Ready R simple funded slow J clear D width grades order shelf k gate q p loss C ep ready deep aged m := by
  let edge := Burn.horizon k+2
  have purchases : ∀ᶠ m : ℕ in atTop,∀ (n : Fin (edge+1)), localOpen (n.val) ≤ m ∧ chart (n.val) m := by
    rw [Filter.eventually_all]
    intro n
    exact (eventually_ge_atTop (localOpen (n.val))).and (WilsonReceivedCloseCoveredWalletDates.scheduled R simple funded slow
      J clear D width grades order shelf n.val k gate q p loss C ep)
  filter_upwards [purchases,eventually_ge_atTop (WilsonCenteredCaptureClock.first R simple),eventually_ge_atTop (R.t 0),
    eventually_ge_atTop early,eventually_ge_atTop late,eventually_ge_atTop saved,
    R.alloy.B.a.fits.deep.eventually_ge_atTop (max shelf (max k q))] with m all first t₀ reporter kiosk hard stage
  intro i mi
  have fit := stage.trans (R.alloy.B.a.fits.mono mi)
  refine ⟨first.trans mi,t₀.trans mi,reporter.trans mi,kiosk.trans mi,(le_max_left ..).trans fit,
    ((le_max_left ..).trans (le_max_right ..)).trans fit,((le_max_right ..).trans (le_max_right ..)).trans fit,hard.trans mi,?_⟩
  intro seats load
  have paid:=all ⟨seats,Nat.lt_succ_of_le load⟩
  exact ⟨paid.1.trans mi,fun j ij=>paid.2 j (mi.trans ij)⟩

end YM.Integration.WilsonReceivedGeometricPriorDates
