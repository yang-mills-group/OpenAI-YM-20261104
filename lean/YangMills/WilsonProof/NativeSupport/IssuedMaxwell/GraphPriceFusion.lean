import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphTender
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphSpectralTail
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphPriceFusion
open YM YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.FVA2.O YM.FVA2.O.Project
open YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation
open scoped BigOperators Classical
variable (g:YangMills.GaugeGroup){n m:ℕ}{I:Type}[Fintype I]

theorem held (b:Fin m→Ordinary.Label (B g))(w k:ℕ)(x:Points (m+1))(c:I→ℂ)(v:I→Sec g.core w):
    read g (m+1) k (Fin.cons ⟨w,∑i,c i • v i⟩ b) x=
      ∑i,c i*read g (m+1) k (Fin.cons ⟨w,v i⟩ b) x:=by
  obtain ⟨f,line⟩:=GraphFirstPort.original g b w k x
  simp_rw [line]
  calc
    f (∑i,c i • v i)=∑i,f (c i • v i):=map_sum f _ _
    _=_:=Finset.sum_congr rfl fun i _=>f.map_smul (c i) (v i)

theorem original (c:I→ℂ)(p:I→FLog g.core n)(b:Fin m→Ordinary.Label (B g))
    (e h k:ℕ)(t:ℝ)(x:Points n)(y:Points m):
    Ordinary.truncation (B g) (read g) (GraphPrices.entered g (GraphTender.combine c p)) e h k b t x y=
    ∑i,c i*Ordinary.truncation (B g) (read g) (GraphPrices.entered g (p i)) e h k b t x y:=by
  let node:Points (m+1):=WithLp.toLp 2 (Fin.cons 0 y.ofLp)
  let scale (w:Fin (h+1)):ℂ:=Real.exp (((e:ℝ)-(w.val:ℝ))*t)
  let plate (w:Fin (h+1))(j:Fin (k+1))(i:I):ℂ:=
    scale w*read g (m+1) (k-j.val) (Fin.cons ⟨w.val,GraphPrices.entered g (p i) w.val j.val t x⟩ b) node
  calc
    _=∑w,∑j,∑i,c i*plate w j i:=by
      unfold Ordinary.truncation
      refine Finset.sum_congr rfl fun w _=>?_
      refine Finset.sum_congr rfl fun j _=>?_
      rw [GraphTender.posting]
      let earlier (i:I):Sec g.core w.val:=GraphPrices.entered g (p i) w.val j.val t x
      have sold:=held g b w.val (k-j.val) node c earlier
      calc
        _=scale w*(∑i,c i*read g (m+1) (k-j.val) (Fin.cons ⟨w.val,earlier i⟩ b) node):=
          congrArg (fun z:ℂ=>scale w*z) sold
        _=_:=by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _=>?_
          change scale w*(c i*_) =c i*(scale w*_)
          ring
    _=∑i,∑w,∑j,c i*plate w j i:=GraphSpectralTail.corners _
    _=_:=by
      refine Finset.sum_congr rfl fun i _=>?_
      simp only [Ordinary.truncation,Finset.mul_sum,plate,scale,node]
end IssuedMaxwell.GraphPriceFusion
end
