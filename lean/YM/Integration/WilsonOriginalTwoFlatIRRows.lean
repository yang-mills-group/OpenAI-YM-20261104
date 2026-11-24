import YM.Integration.WilsonOriginalTwoFlatIRRowFields
import YM.Integration.WilsonOriginalTwoFlatIRClock

/-! The original adjacent-scale price at capture. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRRows
open Function Filter Finset Lattice Wilson RG PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
theorem nextClock (simple:G.Simple):∀ᶠ c:ℕ in atTop,∀N per,c<N→
    R.alloy.B.a.clock.hatBeta (c+1)≤(3*(regulatorRun R.family N per c)⁻¹)^2:=by
  filter_upwards [RG01.Physical.nextHat simple R.alloy.B.a] with c neighbor N per cut
  have pos:0<R.family.path.β N per c:=Overlay.beta_positive R.makes.wilson cut.le
  have base: R.alloy.B.a.clock.hatBeta c/2≤R.family.path.β N per c:=(R.makes.wilson.represents N per c cut.le).band.1
  change R.alloy.B.a.clock.hatBeta (c+1)≤(3*(Real.sqrt (R.family.path.β N per c))⁻¹⁻¹)^2
  rw [inv_inv,mul_pow,Real.sq_sqrt pos.le]
  change R.alloy.B.a.clock.hatBeta (c+1)≤2*R.alloy.B.a.clock.hatBeta c at neighbor
  linarith only [base,neighbor,pos]

end YM.Integration.WilsonOriginalTwoFlatIRRows
