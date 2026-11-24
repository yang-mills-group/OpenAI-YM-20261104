import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.QuadraticLabel
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.CubicLabel
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.NativePupil
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.NativeTriangle
open YM YM.XSpace YM.XSpace.Normalize YangMills.MSbar
open IssuedMaxwell.Reports (B)
variable {g:YangMills.GaugeGroup}{V:Store g.core}

def triangle (K:Rose.Pick V):Position.Triangle (B g) where
  T:=Rose.toll g.core
  U:=QuadraticLabel.lower g
  UatSix:=Rose.tin g.core
  sameU:=QuadraticLabel.inclusion g
  unit:=leaf g.core 6
  unitValue:=rfl
  cubic:=CubicLabel.original g
  quadratic:=QuadraticLabel.original g
  cut:=K.cut
  profile:=NativePupil.profile K

theorem original (K:Rose.Pick V)(nonneg:∀x,0≤K.image x):(triangle K).Admissible:=by
  obtain ⟨sign,turns,gap,slope⟩:=NativePupil.original K nonneg
  exact ⟨fun x=>(sign x).1,fun x=>(sign x).2,turns,gap,slope⟩
end IssuedMaxwell.NativeTriangle
end
