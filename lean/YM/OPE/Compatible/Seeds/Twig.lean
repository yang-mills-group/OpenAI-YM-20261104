import YM.OPE.Compatible.Nectar.Carousel
import YM.OPE.Compatible.Woods.Frost
/-!
# Projections to native Script axes. Whole map furnished by Warm. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Labels Tensor WithLp Exterior Matrix FreeResolvent Precision Tree AnalyticBridge.LocalGaussianLaws.Current Woody Bloch Work.F08
open scoped Topology BigOperators Classical
variable {r d m n:ℕ}{U:ℝ}{V I W:Type*}{G:Gauge}{c f L:Side}
namespace Script
open Page
-- map slots
abbrev station (G: Gauge)(n:Side):Site n × Shade G ≃ FreeResolvent.Slot G n 1:= Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr axisEquiv (Equiv.refl _)) -- Slot ambiguous
def deckW (G:Gauge)(n:Side):Vec G n 1≃ₗ[ℝ] deck (Shade G) n:= { toFun v:= v ∘ station G n, invFun v:=v ∘ (station G n).symm, left_inv v:=funext fun i=>congr_arg v ((station G n).apply_symm_apply i), right_inv v:=funext fun i=> congr_arg v ((station G n).symm_apply_apply i), map_smul' _ _:=rfl, map_add' _ _:=rfl} -- lemma check
lemma shipEq (v:Vec G c 1)(i): deckW G c v i= v (station G c i):=rfl
lemma slopeCliff (u:Vec G c 0): deckW G c (FreeResolvent.gradient u)=cliff fun p=> component u p.2 (p.1,vac):=by
    ext i; rw [shipEq]; change component (FreeResolvent.tensor G (Exterior.d 0 c) *ᵥ u) i.2.2 (i.1,coord i.2.1)=_; rw [component_mul,d_sites];rfl
-- axis scalar tensor images
lemma idle {S:StepData c f} (P:Cross S.ratio.count (TypeFace 1) (TypeFace 1)) : installed S.ratio (chrome G.ColorIndex P)=(FreeResolvent.tensor G (installed S.ratio P)).submatrix (station G f) (station G c):=by
   ext i j; rw [Matrix.submatrix_apply]; change _= if _=_ then installed _ _ _ _ else 0; by_cases h:i.2.2=j.2.2
   · rw [if_pos (show (station G f i).2.2=(station G c j).2.2 from h)]; rw [installed_sift, installed_sift]; unfold sift; apply tsum_congr; intro v; unfold chrome; erw [if_pos h]; rfl -- sift namespace
   rw [if_neg (show (station G f i).2.2≠(station G c j).2.2 from h)]; rw [installed_sift]; unfold sift; simp [chrome,h]
lemma stage_mul {S:StepData c f} (P:Cross S.ratio.count (TypeFace 1) (TypeFace 1))(w:deck (Shade G) c):
    installed S.ratio (chrome G.ColorIndex P) *ᵥ w= deckW G f (FreeResolvent.tensor G (installed S.ratio P) *ᵥ ((deckW G c).symm w)):=by
    ext1 i; rw [idle,shipEq]; unfold Matrix.mulVec dotProduct; let p:=station G f i
    change (∑ j,(FreeResolvent.tensor G (installed S.ratio P)) p (station G c j)*w j)=_; exact Fintype.sum_equiv (station G c) _ _ fun k=>mul_eq_mul_left_iff.mpr (Or.inl (show w k= (deckW G c) ((deckW G c).symm w) k from congr_fun ((deckW G c).apply_symm_apply w).symm k))
end Script
end YM.OPE.Flume
