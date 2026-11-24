import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.LocatedLabels
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.QuadraticLabel
open YM YM.Maxwell YM.Maxwell.Free YM.XSpace YM.XSpace.Normalize YM.XSpace.Chiral
open YangMills.MSbar.Position
open IssuedMaxwell.Reports (B)
open scoped BigOperators InnerProductSpace
variable (g:YangMills.GaugeGroup)
def lower : Sec g.core 4:=(Rose.f:ℂ)^2 • en (le_refl 4) (Ufield g.core)
theorem inclusion : (Rose.tin g.core).val=(lower g).val:=rfl

theorem original (X:TaylorTower g.core):probe X (lower g).val=(quadraticValue (B g) X:ℂ):=by
  change probe X ((Rose.f:ℂ)^2 • U g.core)=_
  rw [understand]
  simp only [map_smul,map_sum,basicTeam,smul_eq_mul]
  rw [LocatedLabels.quadratic]
  simp only [LocatedLabels.value,real_inner_smul_left,real_inner_smul_right]
  push_cast
  simp only [← Finset.mul_sum]
  ring
end IssuedMaxwell.QuadraticLabel
end
