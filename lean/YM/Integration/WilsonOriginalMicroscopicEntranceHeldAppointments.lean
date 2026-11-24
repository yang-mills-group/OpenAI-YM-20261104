import YM.Integration.WilsonOriginalMicroscopicEntranceHeldMaster
import YM.Integration.WilsonOriginalMicroscopicEntranceHeldMeshClock

/-! One original optical and radial onset precedes both regulators and all field evaluations. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldAppointments
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6


open Filter RG05Readout WilsonThermometerOwnOffsetTale
open WilsonOriginalAlternativeTrialFunded (cold earlier)
open WilsonOriginalAlternativeTrialPhaseSalary (share share_pos)
open WilsonMeasuredPublicEntranceMeshClock (allowance nonneg)
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {V:Type} [Fintype V] [DecidableEq V] (grades:V → ℕ)
  (simple:G.Simple) (pace:WilsonWindowReportingPace.Slow R.kit)
  (nested:WilsonPositionProgramNestedLengths.Nested R.rolls) (cater:Cater R.family R.doors)
  (bank:WilsonThermometerClusterProjectionBudget.Ready R.family.path.levels)
  (forecast:WilsonReportLampForecast.Ready R.family.path.levels) (shop:RG05Preconstruction.ReadoutPurchase R.b)
  (n apron requested t span power:ℕ) (B:ℝ) (degree target:ℕ) (np:0<n) (size:Fintype.card V≤n)
local notation "ord" => WilsonMeasuredPublicEntranceFixedBill.order

def Dates (j:ℕ):Prop:=
  WilsonOriginalAlternativeTrialOwnerCourse.earliest R grades pace forecast simple span ≤ j ∧
  WilsonOriginalAlternativeTrialPaidCourse.floorAge R grades pace forecast simple span power B ≤ j ∧
  (eventually_atTop.mp (WilsonOriginalMicroscopicEntranceHeldPooled.original R grades simple pace nested cater
    forecast shop n apron (ord requested) t t np size (WilsonOriginalAlternativeTrialOwnerClock.allowance power span B)
    (allowance apron) (WilsonOriginalAlternativeTrialPeerPurchase.allowance power span B) (nonneg apron))).choose ≤ j ∧
  cold (V:=V) R simple power span (ord requested) (allowance apron) (share V 1) (nonneg apron)
    (share_pos V zero_lt_one)+1 ≤ j ∧
  earlier (V:=V) R simple power span (ord requested) (allowance apron) (share V 1) (nonneg apron)
    (share_pos V zero_lt_one) ≤ j ∧
  WilsonCenteredCaptureClock.first R simple ≤ j ∧
  (eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple
    (ord requested+WilsonAddressedFiniteGuardCapital.power R grades power univ) zero_lt_one)).choose ≤ j ∧
  (eventually_atTop.mp (WilsonOriginalMicroscopicEntranceHeldRadialMeter.original R grades simple B 2 (by norm_num) requested)).choose ≤ j ∧
  (WilsonMeasuredPublicEntrancePrescribedCampus.original R simple shop grades
    (fun v=>WilsonMeasuredPublicEntranceFixedBill.depth grades (ord requested)+grades v)).choose ≤ j ∧
  (eventually_atTop.mp (WilsonOriginalMicroscopicEntranceDoseRadial.original R simple degree target)).choose ≤ j ∧
  (∀v b,b ≤ grades v → R.family.ref b ≤ j)

theorem original : ∀ᶠ j:ℕ in atTop,
    Dates R grades simple pace nested cater forecast shop n apron requested t span power B degree target np size j:=by
  let cap:=(univ:Finset V).sup grades
  have refs:∀ᶠ j:ℕ in atTop,∀v b,b ≤ grades v → R.family.ref b ≤ j:=by
    filter_upwards [eventually_ge_atTop ((Finset.range (cap+1)).sup R.family.ref)] with j arrived
    intro v b cost
    have small:grades v ≤ cap:=Finset.le_sup (f:=grades) (mem_univ v)
    exact (Finset.le_sup (f:=R.family.ref) (mem_range.mpr (Nat.lt_succ_of_le (cost.trans small)))).trans arrived
  dsimp only [Dates]
  exact (eventually_ge_atTop _).and ((eventually_ge_atTop _).and ((eventually_ge_atTop _).and ((eventually_ge_atTop _).and ((eventually_ge_atTop _).and ((eventually_ge_atTop _).and ((eventually_ge_atTop _).and ((eventually_ge_atTop _).and ((eventually_ge_atTop _).and ((eventually_ge_atTop _).and (refs))))))))))

end YM.Integration.WilsonOriginalMicroscopicEntranceHeldAppointments
end
