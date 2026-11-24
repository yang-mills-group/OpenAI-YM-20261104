import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.NativePrepared
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.NativeTriangle
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.NativeMenu
open YM YM.XSpace YM.XSpace.Normalize YangMills.MSbar
open IssuedMaxwell.Reports (B)
variable (g:YangMills.GaugeGroup)

theorem original (h:g.core.Simple):Nonempty {P:PositionPrescription (B g)//Admissible P}:=by
  obtain ⟨V⟩:=equipped h
  obtain ⟨K,nonneg⟩:=PositiveCut.original (Initialize.standard g.core) h V
  let P:PositionPrescription (B g):=⟨NativeWindows.display V,NativeTriangle.triangle K⟩
  refine ⟨P,NativePrepared.original V,NativeTriangle.original K nonneg,?_⟩
  intro i
  dsimp only
  intro x hx a b hab
  exact K.grants i hx a b hab

def registered (h:g.core.Simple):{P:PositionPrescription (B g)//Admissible P}:=
  nominatedMenu (original g h)
end IssuedMaxwell.NativeMenu
end
