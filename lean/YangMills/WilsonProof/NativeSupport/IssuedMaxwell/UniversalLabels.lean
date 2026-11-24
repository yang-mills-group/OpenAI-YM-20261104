import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.NativeTriangle
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.UniversalLabels
open YM YM.Maxwell YM.Maxwell.Free YM.XSpace YM.XSpace.Normalize YangMills.MSbar
open IssuedMaxwell.Reports (B)
variable (g:YangMills.GaugeGroup)

theorem original (t:Position.Triangle (B g)):
    t.T=Rose.toll g.core ∧ t.U=QuadraticLabel.lower g ∧
    t.UatSix=Rose.tin g.core ∧ t.unit=leaf g.core 6:=by
  have cubic:t.T.val=(Rose.toll g.core).val:=by
    apply equalPol
    intro X
    exact (t.cubic X).trans (CubicLabel.original g X).symm
  have quad:t.U.val=(QuadraticLabel.lower g).val:=by
    apply equalPol
    intro X
    exact (t.quadratic X).trans (QuadraticLabel.original g X).symm
  exact ⟨Subtype.ext cubic,Subtype.ext quad,
    Subtype.ext (t.sameU.trans (quad.trans (QuadraticLabel.inclusion g).symm)),Subtype.ext t.unitValue⟩
end IssuedMaxwell.UniversalLabels
end
