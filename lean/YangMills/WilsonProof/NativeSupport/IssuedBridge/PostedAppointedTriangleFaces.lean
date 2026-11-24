import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.ElectedPrescription
noncomputable section
namespace IssuedBridge.PostedAppointedTriangleFaces
open YangMills YangMills.MSbar YM YM.Maxwell YM.Maxwell.Free YM.XSpace YM.XSpace.Normalize
variable (g : YangMills.GaugeGroup)
variable (t : YangMills.MSbar.Position.Triangle (IssuedMaxwell.Reference.issued g))
theorem cubic : t.T = Rose.toll g.core := by
  apply Subtype.ext
  apply YM.Maxwell.equalPol
  intro A
  exact (t.cubic A).trans (IssuedMaxwell.CubicLabel.original g A).symm
theorem quadratic : t.UatSix = Rose.tin g.core := by
  apply Subtype.ext
  rw [t.sameU, IssuedMaxwell.QuadraticLabel.inclusion g]
  apply YM.Maxwell.equalPol
  intro A
  exact (t.quadratic A).trans (IssuedMaxwell.QuadraticLabel.original g A).symm
theorem unit : t.unit = leaf g.core 6 := by
  apply Subtype.ext
  exact t.unitValue
theorem faces (I : Finset (Fin 3)) :
    t.face I = Rose.missing (Rose.tag g.core) I := by
  classical
  unfold YangMills.MSbar.Position.Triangle.face YangMills.MSbar.Position.Triangle.labels
  rw [cubic g t, quadratic g t, unit g t]
  rfl
theorem original (h : g.IsSimple) (I : Finset (Fin 3)) :
    (IssuedMaxwell.ElectedPrescription.prior g h).1.triangle.face I = Rose.missing (Rose.tag g.core) I :=
  faces g _ I
end IssuedBridge.PostedAppointedTriangleFaces
end
