import YM.Integration.WilsonMeasuredPublicEntranceMaster
import YM.Integration.WilsonMeasuredPublicEntranceMeshClock
/-! All numerical appointments for one original finite family precede its sites, cutoffs and periods. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 4300000
set_option maxRecDepth 8192
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceAppointments
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6


open Filter RG05Readout WilsonThermometerOwnOffsetTale
open WilsonOriginalAlternativeTrialCoveredChain (later first)
open WilsonMeasuredPublicEntranceMeshClock (allowance nonneg)
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {V:Type} [Fintype V] [DecidableEq V] (grades:V → ℕ)
  (simple:G.Simple) (pace:WilsonWindowReportingPace.Slow R.kit)
  (nested:WilsonPositionProgramNestedLengths.Nested R.rolls) (cater:Cater R.family R.doors)
  (bank:WilsonThermometerClusterProjectionBudget.Ready R.family.path.levels)
  (forecast:WilsonReportLampForecast.Ready R.family.path.levels) (shop:RG05Preconstruction.ReadoutPurchase R.b)
  (n apron requested t span power:ℕ) (B:ℝ) (np:0<n) (size:Fintype.card V≤n)
local notation "ord" => WilsonMeasuredPublicEntranceFixedBill.order

def Dates (j:ℕ):Prop:=
  WilsonOriginalAlternativeTrialOwnerCourse.earliest R grades pace forecast simple span ≤ j ∧
  WilsonOriginalAlternativeTrialPaidCourse.floorAge R grades pace forecast simple span power B ≤ j ∧
  (eventually_atTop.mp (WilsonMeasuredPublicEntrancePooledEar.original R grades simple pace nested cater bank
    forecast shop n apron 1 (ord requested) t t np size (WilsonOriginalAlternativeTrialOwnerClock.allowance power span B)
    (allowance apron) (WilsonOriginalAlternativeTrialPeerPurchase.allowance power span B) (nonneg apron))).choose ≤ j ∧
  later (V:=V) R simple span power (ord requested) (allowance apron) 1 (nonneg apron) zero_lt_one ≤ j ∧
  first (V:=V) R simple span power (ord requested) (1+Fintype.card V*1) (allowance apron) 1 100 (nonneg apron)
    zero_lt_one ≤ j ∧
  WilsonCenteredCaptureClock.first R simple ≤ j ∧
  (eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple
    (ord requested+WilsonAddressedFiniteGuardCapital.power R grades power univ) zero_lt_one)).choose ≤ j ∧
  (eventually_atTop.mp (WilsonMeasuredPublicEntranceElectedMeter.original R grades simple B requested)).choose ≤ j ∧
  (WilsonMeasuredPublicEntrancePrescribedCampus.original R simple shop grades
    (fun v=>WilsonMeasuredPublicEntranceFixedBill.depth grades (ord requested)+grades v)).choose ≤ j ∧
  (∀v b,b ≤ grades v → R.family.ref b ≤ j)

theorem original : ∀ᶠ j:ℕ in atTop,
    Dates R grades simple pace nested cater bank forecast shop n apron requested t span power B np size j:=by
  let cap:=(univ:Finset V).sup grades
  have refs:∀ᶠ j:ℕ in atTop,∀v b,b ≤ grades v → R.family.ref b ≤ j:=by
    filter_upwards [eventually_ge_atTop ((Finset.range (cap+1)).sup R.family.ref)] with j arrived
    intro v b cost
    have small:grades v ≤ cap:=Finset.le_sup (f:=grades) (mem_univ v)
    exact (Finset.le_sup (f:=R.family.ref) (mem_range.mpr (Nat.lt_succ_of_le (cost.trans small)))).trans arrived
  dsimp only [Dates]
  exact (eventually_ge_atTop _).and ((eventually_ge_atTop _).and ((eventually_ge_atTop _).and
    ((eventually_ge_atTop _).and ((eventually_ge_atTop _).and ((eventually_ge_atTop _).and
      ((eventually_ge_atTop _).and ((eventually_ge_atTop _).and ((eventually_ge_atTop _).and refs))))))))

/-- Taking the common maximum keeps every prescribed finite family before its tests. -/
theorem panels {J:Type}[Fintype J] (grant:J → ℕ → Prop)(paid:∀x,∀ᶠ j:ℕ in atTop,grant x j):
    ∀ᶠ j:ℕ in atTop,∀x,grant x j:=Filter.eventually_all.mpr paid

end YM.Integration.WilsonMeasuredPublicEntranceAppointments
end
