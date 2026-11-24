import YM.Integration.WilsonReceivedCoveredSignedWallet

/-! Fix all five physical angular and folded winding onsets before the cutoff, period and marked positions. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCloseCoveredWalletDates
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
  {V:Type} [DecidableEq V] [Fintype V] (grades:V→ℕ) (order shelf seats k:ℕ)
  (gate:WilsonReportingForestAngularReflection.posted R) (q p loss:ℕ) (C:ℝ) {ε:ℝ} (ep:0<ε)

local notation "n" => order+shelf+2
local notation "chart" => max (WilsonJointAxialRoster.opening R simple funded slow J clear (Fintype.card V) n q ep)
  (WilsonReceivedAxialFiling.opening R simple D φ width order shelf (Fintype.card V) ep)
local notation "finiteReach" => max (WilsonReceivedAxialFinite.opening R simple q ep)
  (WilsonReceivedAxialFinite.massOpening R D grades order shelf seats (k:=k) simple width)
local notation "clock" => (eventually_atTop.mp (WilsonJointAxialClock.original R simple)).choose
local notation "rare" => WilsonJointAxialScalar.opening (V:=V) R simple gate q n (p+loss+1+2*n*(Fintype.card V))
local notation "winding" => (eventually_atTop.mp (WilsonCoveredOrdinaryWeightedPost.original R simple D φ grades
  width order shelf k seats 0 (Fintype.card V) loss (p+1) 1 1 C zero_le_one ep)).choose

def Ready (u₀:ℕ) : Prop := ∀ (i : ℕ), u₀ ≤ i → chart ≤ i ∧ finiteReach ≤ i ∧ clock ≤ i ∧ rare ≤ i ∧ winding ≤ i

theorem scheduled : ∀ᶠ u₀:ℕ in atTop,Ready R simple funded slow J clear D width grades order shelf seats k
    gate q p loss C ep u₀ := by
  filter_upwards [eventually_ge_atTop chart,eventually_ge_atTop finiteReach,eventually_ge_atTop clock,
    eventually_ge_atTop rare,eventually_ge_atTop winding] with u₀ a b c d e
  intro i hi
  exact ⟨a.trans hi,b.trans hi,c.trans hi,d.trans hi,e.trans hi⟩

end YM.Integration.WilsonReceivedCloseCoveredWalletDates
