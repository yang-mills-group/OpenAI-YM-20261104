import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.TriangleAxes
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.NativeColor
open YM YM.Maxwell YM.Maxwell.Free YM.XSpace YM.XSpace.Chiral YM.Lattice
open scoped BigOperators
variable {G:Gauge}
def component (X:TaylorTower G)(k:G.ColorIndex)(a b:Axis):ℝ:=(X 0).val a b (fun _=>0) k

theorem skew (X:TaylorTower G)(k:G.ColorIndex)(a b:Axis):
    component X k a b= -component X k b a:=by
  have h:=(X 0).property.1.antisymmetric a b
  exact congrArg (fun f=>f (fun _=>0) k) h

theorem original (s:Bool)(i:Fin 3)(X:TaylorTower G)(k:G.ColorIndex):
    (available (X 0) (Fq s i)) k=
      ∑b:PlaqAxes,q s i (six b) (endr b)*component X k (six b) (endr b):=by
  change (∑b:PlaqAxes,q s i (six b) (endr b) • cell (six b) (endr b))
      (faceMap 0 (cp (G:=G) k) (X 0))=_
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
  rfl
end IssuedMaxwell.NativeColor
end
