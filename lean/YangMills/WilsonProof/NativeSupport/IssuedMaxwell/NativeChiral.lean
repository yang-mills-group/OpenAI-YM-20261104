import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.NativeColor
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.ChiralFaces
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.TriangleCalibration
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.NativeChiral
open YM YM.Maxwell YM.Maxwell.Free YM.XSpace YM.XSpace.Chiral YangMills.MSbar.Position
open IssuedMaxwell.Reports (B)
open scoped BigOperators InnerProductSpace
variable (g:YangMills.GaugeGroup)

theorem field (s:Bool)(X:TaylorTower g.core)(i:Fin 3):
    chiralField (B g) s X i=(Rose.f:ℝ) • available (X 0) (Fq s i):=by
  apply congrArg (fun v:g.core.Color=>(Rose.f:ℝ) • v)
  ext1 k
  rw [NativeColor.original,ChiralFaces.original _ _ _ (NativeColor.skew X k)]
  cases s <;> rfl

theorem color (a b c:g.core.Color):
    -((g.core.colorMat a*(g.core.colorMat b*g.core.colorMat c-
    g.core.colorMat c*g.core.colorMat b)).trace.re)/(g.core.repDim:ℝ)=
    inner ℝ a (g.core.ad b c):=by
  rw [←g.core.colorMat_ad,g.core.trace_color]
  have h : (g.core.repDim:ℝ)≠0:=by change ((g.n+1:ℕ):ℝ)≠0;positivity
  field_simp

end IssuedMaxwell.NativeChiral
end
