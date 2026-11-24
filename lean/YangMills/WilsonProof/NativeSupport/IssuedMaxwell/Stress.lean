import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Sectors
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.Stress
open YM YM.Maxwell YM.Maxwell.Free
open scoped Classical BigOperators
variable (g:YangMills.GaugeGroup)

def tensor (a b:Axis) : LinearMap.range (observable g.core 4):=
  ⟨-polStress g.core a b,(shellSector g.core 4).neg_mem (stress_label g.core a b)⟩

theorem original (A:YangMills.Maxwell.Coordinates.Tower (IssuedMaxwell.Shell.coordinates g))
    (a b:Axis):
    (IssuedMaxwell.Shell.coordinates g).eval A (tensor g a b).val=
      (IssuedMaxwell.Shell.coordinates g).stressValue A a b:=by
  change probe A (-polStress g.core a b)=_
  simp only [map_neg,polStress,sheetEnergy,map_sub,map_sum,map_smul,measure_phi,
    smul_eq_mul,←Complex.ofReal_sum,←Complex.ofReal_mul,←Complex.ofReal_sub]
  rw [kr_eq]
  rfl
end IssuedMaxwell.Stress
end
