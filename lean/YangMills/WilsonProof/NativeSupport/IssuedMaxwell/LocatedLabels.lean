import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.NativeChiral
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.LocatedLabels
open YM YM.Maxwell YM.Maxwell.Free YM.XSpace YM.XSpace.Chiral YangMills.MSbar.Position
open IssuedMaxwell.Reports (B)
open scoped BigOperators InnerProductSpace
variable (g:YangMills.GaugeGroup)
def held (s:Bool)(X:TaylorTower g.core)(i:Fin 3):g.core.Color:=chiralField (B g) s X i
theorem value (s:Bool)(X:TaylorTower g.core)(i:Fin 3):
    held g s X i=(Rose.f:ℝ) • available (X 0) (Fq s i):=NativeChiral.field g s X i
theorem quadratic (X:TaylorTower g.core):quadraticValue (B g) X=
    (1/2:ℝ)*∑i:Fin 3,inner ℝ (held g false X i) (held g false X i):=rfl
theorem cubic (X:TaylorTower g.core):cubicValue (B g) X=
    ∑i:Fin 3,∑j:Fin 3,∑k:Fin 3,liftedSign i j k*
      inner ℝ (held g true X i) (g.core.ad (held g true X j) (held g true X k)):=by
  change (∑i:Fin 3,∑j:Fin 3,∑k:Fin 3,Cubic.orientation i j k*
      (-((g.core.colorMat (held g true X i))*(g.core.colorMat (held g true X j)*
        g.core.colorMat (held g true X k)-g.core.colorMat (held g true X k)*
        g.core.colorMat (held g true X j))).trace.re/(g.core.repDim:ℝ)))=_
  simp only [TriangleAxes.orientation,NativeChiral.color]
end IssuedMaxwell.LocatedLabels
end
