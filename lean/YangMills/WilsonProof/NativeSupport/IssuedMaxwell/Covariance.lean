import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Shell
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.Covariance
open YangMills YM
open scoped Classical
variable (g:YangMills.GaugeGroup)

theorem green (x:YangMills.Spacetime):YangMills.Maxwell.Coordinates.green x=YM.Maxwell.Green x:=rfl

theorem kernel (a b c d:YangMills.Axis)(x:YangMills.Spacetime):
    YangMills.Maxwell.Coordinates.curvatureKernel a b c d x=YM.Maxwell.bareCurl a b c d x:=rfl

theorem original (p q:YM.Maxwell.Slot g.core)(x y:YangMills.Spacetime):
    (IssuedMaxwell.Shell.coordinates g).covariance p q x y=YM.Maxwell.Wick.entry p q x y:=by
  rfl
end IssuedMaxwell.Covariance
end
