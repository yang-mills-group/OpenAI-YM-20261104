import YM.Integration.WilsonReceivedChronologicalSaleClock
import YM.Integration.WilsonReflectedRelativeDate
/-! The original optical length pays the numerical aperture at its actual moving lower filing. -/
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedAperture
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
include simple in
theorem original (A:ℕ):∀ᶠ m:ℕ in Filter.atTop,∀K:ℕ,
    R.family.S.scale K-R.family.S.scale m≤(A:ℝ)*(1+Real.log (R.family.path.levels.clock.hatBeta (m+1))) →
    R.family.S.a (m+1)/R.family.S.a K≤(R.family.path.levels.clock.hatBeta (m+1))^(2*A):=by
  obtain ⟨first,early⟩:=Filter.eventually_atTop.mp ((RG01.Physical.hats simple R.family.path.levels).eventually_ge_atTop (Real.exp 1))
  filter_upwards [Filter.eventually_ge_atTop first] with m late
  intro K span
  let H:=R.family.path.levels.clock.hatBeta (m+1)
  have hp:0<H:=zero_lt_one.trans (R.family.path.levels.fits.delayed (m+1))
  have one:1≤Real.log H:=by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (early (m+1) (by omega))
  calc
    _ ≤ R.family.S.a m/R.family.S.a K:=div_le_div_of_nonneg_right (R.family.S.strictAnti.antitone (Nat.le_succ m)) (R.family.S.a_pos K).le
    _ ≤ H^(2*A):=by
      apply (Real.log_le_log_iff (div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)) (pow_pos hp _)).mp
      rw [WilsonReflectedRelativeDate.ratio,Real.log_pow]
      calc
        _ ≤ (A:ℝ)*(1+Real.log H):=span
        _ ≤ (A:ℝ)*(Real.log H+Real.log H):=mul_le_mul_of_nonneg_left (by linarith only [one]) (Nat.cast_nonneg _)
        _ = _:=by push_cast;ring
end YM.Integration.WilsonReceivedChronologicalFixedAperture
end
