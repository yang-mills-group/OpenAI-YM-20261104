import YM.Integration.WilsonReceivedChronologicalTwoFlatSale
import YM.Integration.WilsonReceivedClosePhysicalBirths
import YM.Integration.WilsonOriginalCensusFundedAttendance
/-! Uniform dates for the original marked regular, failed-field and compulsory receipts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalSaleClock
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor QuadraticLocal.Affinity
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport Pert.Asymptotics
open WilsonOriginalCensusAngularFace
open scoped BigOperators Classical


open WilsonOriginalFullRosterCouplingClock (work wallet raw)
open WilsonOriginalCensusFundedAttendance (Demand)
variable {G:Gauge}(R:Run G)(simple:G.Simple)
variable {n q p₀:ℕ}{grades:Fin n→ℕ}
local notation "stage" l:max => R.alloy.B.a.clock.J l

structure Regular (n cost P f d p roof:ℕ)(C:ℝ)(b₂:2 ≤ C)(tol:ℝ)(tp:0<tol)(b j:ℕ) : Prop where
  coupling:(eventually_atTop.mp (WilsonOriginalFullRosterCouplingClock.original R simple n cost P f d C
    (zero_le_two.trans b₂))).choose ≤ b
  failed:WilsonOriginalMountedFailedHalo.first R simple n
    (Nat.cast_nonneg (work n P f d+1+(wallet f).pole+(raw d).pole)) tp.le ≤ b
  station:WilsonOriginalFullRosterDatedReturn.station R simple roof n ≤ j
  mature:WilsonCenteredCaptureClock.first R simple ≤ b
  failure:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple p tp)).choose ≤ j+1
  zero:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple 0 (by norm_num:0<(1:ℝ)))).choose ≤ b

theorem regular (n cost P f d p roof:ℕ)(C:ℝ)(b₂:2 ≤ C)(tol:ℝ)(tp:0<tol):
    ∀ᶠ b:ℕ in atTop,∀j ≥ b,Regular R simple n cost P f d p roof C b₂ tol tp b j:=by
  filter_upwards [eventually_ge_atTop ((eventually_atTop.mp (WilsonOriginalFullRosterCouplingClock.original
    R simple n cost P f d C (zero_le_two.trans b₂))).choose),
    eventually_ge_atTop (WilsonOriginalMountedFailedHalo.first R simple n
      (Nat.cast_nonneg (work n P f d+1+(wallet f).pole+(raw d).pole)) tp.le),
    eventually_ge_atTop (WilsonOriginalFullRosterDatedReturn.station R simple roof n),
    eventually_ge_atTop (WilsonCenteredCaptureClock.first R simple),
    eventually_ge_atTop ((eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple p tp)).choose),
    eventually_ge_atTop ((eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple 0
      (by norm_num:0<(1:ℝ)))).choose)] with b coupled failed station mature failure zero
  intro j bj
  exact ⟨coupled,failed,station.trans bj,mature,failure.trans (by omega),zero⟩

local notation "ready" l:max => WilsonMeasuredSemesterSubpower.onset R l (by norm_num:0<(1:ℝ))

structure Compulsory (ask:Demand q p₀ grades)(b j:ℕ) : Prop where
  shelf:ask.shelf ≤ stage (j+1)
  seats:6*ask.school.pieces ≤ stage (j+1)
  one:ready 1 ≤ j+1
  many:ready ask.school.pieces ≤ j+1
  wide:(eventually_atTop.mp ((RG01.Physical.hats simple R.alloy.B.a).eventually_ge_atTop 20)).choose ≤ j+1
  neighbor:(eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ j+1
  fee:WilsonFirstReceivedEarnedFee.opening R simple ask.school.pieces p₀ ask.order ask.vac
    ask.load.deep ask.load.aged (by norm_num:0<(1:ℝ)) ≤ j+1
  group:∀l,b ≤ l → n ≤ stage l
  cap:∀l,b ≤ l → LocalComparison.forcedDivisor R.family l ≤ 1
  rent:∀N per:ℕ,j+1+1 ≤ N →
    (1:ℝ)*(Coat.gStep (R.family.path.rep N per (j+1+1)).beta)^p₀ ≤ 1

theorem compulsory (ask:Demand q p₀ grades):
    ∀ᶠ b:ℕ in atTop,∀j ≥ b,Compulsory R simple ask b j:=by
  have grows:Tendsto R.alloy.B.a.clock.J atTop atTop:=R.family.path.levels.fits.deep
  obtain ⟨height,later⟩:=eventually_atTop.mp (grows.eventually_ge_atTop (max n (max ask.shelf (6*ask.school.pieces))))
  filter_upwards [eventually_ge_atTop height,eventually_ge_atTop (ready 1),eventually_ge_atTop (ready ask.school.pieces),
    eventually_ge_atTop ((eventually_atTop.mp ((RG01.Physical.hats simple R.alloy.B.a).eventually_ge_atTop 20)).choose),
    eventually_ge_atTop ((eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose),
    eventually_ge_atTop (WilsonFirstReceivedEarnedFee.opening R simple ask.school.pieces p₀ ask.order ask.vac
      ask.load.deep ask.load.aged (by norm_num:0<(1:ℝ))),
    eventually_ge_atTop (WilsonSingleHardRadius.first R simple),
    eventually_ge_atTop ((eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose)] with
    b raised one many wide neighbor fee forced cold
  intro j bj
  have high:=later (j+1) (by omega)
  refine ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,?_,?_,?_⟩
  · intro l lb
    have deep:=later l (by omega)
    omega
  · intro l lb
    exact (WilsonSingleHardRadius.half R simple (forced.trans lb)).trans (by norm_num)
  · intro N per nCut
    have temp:=(eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose_spec
      (j+1+1) (by omega) N per nCut
    have small:Pert.Asymptotics.regulatorRun R.family N per (j+1+1) ≤ 1:=by linarith only [temp.1,temp.2]
    rw [one_mul]
    exact pow_le_one₀ (ActualRunKernelPackets.regulator_pos R N per _ nCut).le small

end YM.Integration.WilsonReceivedChronologicalSaleClock
end
