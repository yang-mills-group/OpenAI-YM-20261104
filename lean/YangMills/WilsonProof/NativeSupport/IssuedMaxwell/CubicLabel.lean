import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.LocatedLabels
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.CubicLabel
open YM YM.Maxwell YM.Maxwell.Free YM.XSpace YM.XSpace.Normalize YM.XSpace.Chiral
open YangMills.MSbar.Position IssuedMaxwell.Reports
open scoped BigOperators InnerProductSpace
variable (g:YangMills.GaugeGroup)
theorem original (X:TaylorTower g.core):probe X (Rose.toll g.core).val=(cubicValue (B g) X:ℂ):=by
  change probe X ((Rose.f:ℂ)^3 • Chiral.B g.core)=_
  rw [map_smul,fuelled]
  rw [LocatedLabels.cubic]
  simp only [LocatedLabels.value,map_smul,LinearMap.smul_apply,real_inner_smul_left,real_inner_smul_right]
  push_cast
  simp only [smul_eq_mul,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun k _=>?_
  ring
end IssuedMaxwell.CubicLabel
end
