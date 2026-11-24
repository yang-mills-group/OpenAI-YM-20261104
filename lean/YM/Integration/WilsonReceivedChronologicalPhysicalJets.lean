import YM.Integration.WilsonReceivedChronologicalPanelClock
/-! The actual temperature of an already appointed mixed finite panel at a dated receiving edge. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalPhysicalJets
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


private theorem thermal {h β:ℝ}(four:4≤h)(pos:0<β)(bound:β≤4*h){p w:ℕ}(fit:w≤p):
    (h^p)⁻¹≤((Real.sqrt β)⁻¹)^w:=by
  have one:1≤h:=by linarith
  have square:β≤h^2:=bound.trans (by simpa only [pow_two] using mul_le_mul_of_nonneg_right four (zero_le_one.trans one))
  have inv:h⁻¹≤(Real.sqrt β)⁻¹:=inv_anti₀ (Real.sqrt_pos.mpr pos)
    (Real.sqrt_le_iff.mpr ⟨zero_le_one.trans one,square⟩)
  rw [←inv_pow]
  exact (pow_le_pow_of_le_one (inv_nonneg.mpr (zero_le_one.trans one)) (inv_le_one_of_one_le₀ one) fit).trans
    (pow_le_pow_left₀ (inv_nonneg.mpr (zero_le_one.trans one)) inv _)
theorem original (ask:Demand q p₀ grades){b j:ℕ}
    (clock:WilsonReceivedChronologicalSaleClock.Compulsory R simple ask b j)
    (N per:ℕ)(live:j+1<N)(p w:ℕ)(fitted:w ≤ p):
    ((R.family.path.levels.clock.hatBeta (j+1))^p)⁻¹ ≤ (regulatorRun R.family N per (j+1+1))^w:=by
  have four:= (eventually_atTop.mp ((RG01.Physical.hats simple R.alloy.B.a).eventually_ge_atTop 20)).choose_spec (j+1) clock.wide
  have next:=(eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose_spec (j+1) clock.neighbor
  have band:=(R.makes.wilson.represents N per (j+1+1) live).band
  have pos:0<R.family.path.β N per (j+1+1):=(half_pos (zero_lt_one.trans
    (R.alloy.B.a.fits.delayed (j+1+1)))).trans_le band.1
  apply thermal (le_trans (by norm_num:4≤(20:ℝ)) four) pos _ fitted
  apply band.2.trans
  change 2*R.alloy.B.a.clock.hatBeta (j+1+1) ≤ 4*R.alloy.B.a.clock.hatBeta (j+1)
  linarith only [next]

end YM.Integration.WilsonReceivedChronologicalPhysicalJets
end
