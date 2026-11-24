import YM.OPE.Compatible.Basin.Cinque
/-!
# Active tallies in one alphabet on fine and coarse sites.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Tree Exterior Stationary Woody
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Q E:Type*} {G:Gauge}{n m l c f:Side}{S:StepData c f} {r:Ratio c f}
namespace Script
open Page Virgin Work.F05
def spool (G:Gauge)(n:Side): Bid.Dir G n ≃L[ℝ] deck (Shade G) n:= LinearEquiv.toContinuousLinearEquiv {
     toFun v i:= v (i.1,coord i.2.1) i.2.2
     invFun p i:= toLp 2 fun j=> p (i.1,(axisEquiv.symm i.2,j))
     left_inv p:= by ext i j; change p (i.1,axisEquiv (axisEquiv.symm i.2)) j= _; rw [Equiv.apply_symm_apply]
     right_inv p:= by ext i; change p (i.1,(axisEquiv.symm (axisEquiv i.2.1),i.2.2))=_; rw [Equiv.symm_apply_apply]
     map_add' _ _ := rfl
     map_smul' _ _:=rfl }
lemma primora (G:Gauge)(N:Side)(v: Bid.Dir G N):primU G (spool G N v)=represent v:=by
     ext1 i; change G.lieExp _ = G.lieExp (v (i.1,coord i.2)) * 1; rw [mul_one]; apply congr_arg; ext j; change (spool G N v) (0 +wrap N (lift i.1),i.2,j)=_; rw [wrap_lift, zero_add]; rfl
abbrev Tile (G:Gauge) (L:Side):= Shade G⊕ Slip G L
def fromAxis (F:Forest r): AxisChart G F ≃L[ℝ] (Active G F →ℝ):= (countingBasis F G).equivFun.toContinuousLinearEquiv -- expects S?
def belt (r: Ratio c f) (h:Odd r.count.val)(G:Gauge): AxisChart G (forest r h)≃L[ℝ] deck (Slip G r.count) c:= (fromAxis _).trans (LinearEquiv.funCongrLeft ℝ ℝ (squad r h G).symm).toContinuousLinearEquiv -- direction
lemma belt_read (r:Ratio c f) (h:Odd r.count.val)(G:Gauge)(p:AxisChart G (forest r h))(v:Active G (forest r h)):(belt r h G p) (squad r h G v)= cash (countingBasis (forest r h) G) p v:=by
    change cash (countingBasis (forest r h) G) p ((squad r h G).symm (squad r h G v))= _; rw [Equiv.symm_apply_apply]
variable (r) (h:Odd r.count.val)
def dose [Fintype I][Fintype J](N:Side): (deck I N × deck J N)≃L[ℝ] deck (I⊕J) N:=LinearEquiv.toContinuousLinearEquiv {
    toFun p j:= match j.2 with | .inl i=> p.1 (j.1,i)| .inr i=>p.2 (j.1,i)
    invFun p:= (fun i=> p (starI i),fun i=>p (starJ i))
    left_inv p:=rfl
    right_inv p:=by ext1 ⟨i,j|j⟩<;> rfl
    map_add' v w:=by ext1 ⟨i,j|j⟩<;>rfl
    map_smul' _ _:=by ext1 ⟨i,j|j⟩<;> rfl }
local notation "F"=>forest r h
abbrev vertP (G:Gauge):= Bid.Dir G c × AxisChart G F
-- bundling F via Π gauge
abbrev paintV (G:Gauge):(Bid.Dir G c × AxisChart G F)≃L[ℝ] deck (Tile G r.count) c:= (ContinuousLinearEquiv.prodCongr (spool G c) (belt r h G)).trans (dose c)
lemma petalV (p:Bid.Dir G c × AxisChart G F)(i: Active G F): paintV r h G p (starJ (squad r h G i))=cash (countingBasis F G) p.2 i:= belt_read r h G p.2 i
lemma bolt_pin (v:Active G F): paintV r h G (0,(countingBasis F G) v)= deltaH (starJ (squad r h G v)) := by
     apply funext; intro i; rcases i with ⟨i,j|j⟩
     · change spool G c 0 (i,j)= deltaH (starJ (I:=Shade G) (squad r h G v)) (starI (i,j)); rw [map_zero]; simp [deltaH,starI,starJ]
     obtain ⟨u,hu⟩:= (squad r h G).surjective (i,j); let T:=squad r h G; change paintV r h G _ (starJ (i,j))=deltaH _ (starJ (i,j));rw [← hu,petalV]; change cash (countingBasis F G) _ u=deltaH (starJ (I:=Shade G) (T v)) (starJ (T u)); by_cases H:v=u
     · subst v; simp [deltaH,cash]
     have hp : starJ (I:=Shade G) (T u)≠ starJ (T v):=fun e=> H (T.injective (Prod.ext (Prod.mk.inj e).1 (Sum.inr.inj (Prod.mk.inj e).2))).symm; simp [deltaH,hp,cash,H]
end Script
end YM.OPE.Flume
