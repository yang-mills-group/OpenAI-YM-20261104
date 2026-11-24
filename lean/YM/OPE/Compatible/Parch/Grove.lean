import YM.OPE.Compatible.Parch.Bosun
/-!
# Census. Currencies with support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Claw
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score Tree Woody Next.Free FreeResolvent
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver Tensor
open Drift Char Silt Silt.Float Module Variance Merchant Merchant.SiteL Stand
variable {i j d k m r l:ℕ}{n:Side}{K:Sponsor G}{T:Seasons K}{v:ℝ}
section
variable {E F X Z:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F]
namespace Tall
lemma map (P:F→L[ℝ] E){p:E→ℝ}(h:Tall p d):Tall (p∘P) d:=by
        obtain ⟨Q,h⟩:= stock h; let t(j:ℕ):= (Q j).compContinuousLinearMap (fun _=>P); rw[h]
        rw[show ((∑ j∈range (d+1),diagonal (Q j)) ∘ P)=(fun i=> ∑ j∈range (d+1),Tensor.diagonal (t j) i) from funext fun i=>by unfold Function.comp; rw [Finset.sum_apply];rfl]; exact tall_of t
variable {A:E→Type*}
end Tall
end
section
variable {D V W X:Type}[Fintype D][Fintype W] [NormedAddCommGroup X][NormedSpace ℝ X]
variable (R:Cascade.Score D V) (L:Libra.Keys G D→ₗ[ℝ] Dual' (Libra.Keys G D))(F:Libra.Keys G W→L[ℝ] Libra.Keys G D)(P:Law (Libra.Keys G W))
open FoldU
namespace OrientX
-- diagonal pose (ext)
noncomputable def ρX (g:(Libra.Keys G D)→ℝ)(r:ℕ):(Libra.Keys G D)→ℝ:=rank g (r+1) ∘ mate F L P
-- contour locality for solving(λ not visible)
variable (U:(Libra.Keys G D)→L[ℝ] X) (g:(Libra.Keys G D)→ℝ)
omit [NormedAddCommGroup X] [NormedSpace ℝ X] in lemma wreathe (t:ℝ)(x:(Libra.Keys G D)):ρX L F P g r (t • x) = t^(r+1) • ρX L F P g r x:=by unfold ρX; rw [Function.comp_apply,map_smul]; exact Tensor.homogeneous ..
omit [NormedAddCommGroup X] [NormedSpace ℝ X] in lemma diana (r:ℕ):rank (ρX L F P g r) (r+1)=ρX L F P g r:=by
       let Q:= ρX L F P g r; apply Tall.pint; exact (Tensor.diag_smooth (Tensor.coeff g (r+1) 0) _).comp (mate F L P).contDiff; exact fun x t=> wreathe ..
variable (h:OrientX R L F P)
include h
omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma sun₀ (r:ℕ) (hp:LevelA R g)(he:ContDiffAt ℝ ω g 0): LevelA R (ρX L F P g r)∧∀ x:(Libra.Keys G D),∀ y:(Libra.Keys G W),ρX L F P g r (x+F y)=ρX L F P g r x:=by
       let U:=hp.rankY R he (r+1); refine ⟨⟨fun x v=>?_,fun y k=>?_⟩,fun x y=>?_⟩ <;>unfold ρX<;>simp only [Function.comp_apply]
       · rw [h.slide, U.tilts]
       · rw [h.city,U.inherits]
       rw [map_add, twin F L P h.hyst, add_zero]
omit h
variable (hx:∀ i j:(Libra.Keys G D),U i=U j→ g i=g j)
variable (hv:∀ i j:(Libra.Keys G D),U i=U j→ pour F L P i=pour F L P j) (hp:ContDiffAt ℝ ω g 0)
include hv
lemma veil (x y:(Libra.Keys G D))(he:U x=U y): U (mate F L P x)=U (mate F L P y):=by unfold mate; rw [_root_.sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,_root_.sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply, hv _ _ he,map_sub,map_sub,he]
include hx hp
lemma rimE (x y:(Libra.Keys G D))(he:U x=U y)(r:ℕ):ρX L F P g r x=ρX L F P g r y:=
        crossD g hp hx _ _ (fun _=>veil L F P U hv _ _ he)
local notation "VD"=>Fin (r+1)
lemma remN (x y:(Libra.Keys G D))(he:U x=U y):νrt L F P g r x=νrt L F P g r y:=by
        unfold νrt ν; congr 1; apply LinearMap.ext; intro z; let T:=Tensor.coeff g (r+1) 0; let v:=mate F L P; change (∑ i:VD,T (tab x (v x) i (F z)))=∑ i:VD,T (tab y (v y) i (F z)); apply sum_congr rfl; intro i _; refine crossD _ hp hx _ _ (fun j=>?_); unfold tab FoldU.banner rowP; by_cases hj:j=i; · subst j;simp
        rw [update_of_ne hj, update_of_ne hj]; split<;> first|exact he|exact veil L F P U hv x y he
end OrientX
end
end YM.OPE.Claw
