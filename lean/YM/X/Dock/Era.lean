import YM.X.Dock.Spree
/-!
# flow at second leg, descended in second-leg variable. labels are ps, mn NOT normalized. express integration by parts.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir.Dock
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset MeasureTheory Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Imprint CellsInt Beamer Asymptotics Crate.Fund
open Maxwell (Green normal grad)
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {m k d:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R e c:ℝ}
local notation "ε"=> epsilon q
local notation "L"=>(atTop:Filter ℕ)
abbrev Aster (r:ℝ)(p:Tet)(i:Axis)(x:E4):= ∑ j:Axis, form r p j i * Maxwell.grad j Green x
abbrev pull (i:Axis)(f:E4→ℝ):E4→ℝ:= -Maxwell.grad i f
variable (t:ℝ)(u v w:Tet)(i j:Axis)
lemma smoothA (x:E4)(hx:x≠0): ContDiffAt ℝ ∞ (Aster t u j) x := ContDiffAt.sum (fun i _=> contDiffAt_const.mul (Maxwell.gradGradientSmooth hx i)) -- function notation adapt
lemma sized (x:E4)(hx:x≠0): pull i (Aster t u j) x= ∑ k:Axis, form t u k j * (-(Maxwell.grad i (Maxwell.grad k Green) x)):= by unfold Aster pull; rw [Pi.neg_apply, Maxwell.grad_sum (fun k x=>form t u k j * Maxwell.grad k Green x) (fun i=>contDiffAt_const.mul (Maxwell.gradGradientSmooth hx i)) i,← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun k _=>?_ ; rw [Maxwell.grad, YM.Analysis.D, show fderiv ℝ (fun x=>form t u k j*Maxwell.grad k Green x) x= _ from ((((Maxwell.gradGradientSmooth hx k).differentiableAt (by simp)).hasFDerivAt).const_mul (form t u k j)).fderiv];simp [Maxwell.grad,YM.Analysis.D]
lemma symbol (x:E4)(hx:x≠0): Aster (-1) u i x=Cup u i x:= by unfold Aster Cup;simp only [Maxwell.first_Green hx];rfl
-- Off second argument derivative 
def spliceG (i:Axis)(x y:E4)(s:ℝ)(p:Tet)(j:Axis):ℝ:= pull i (Aster s p j) (x-y)
lemma sectionG (x y:E4)(hx:x≠y): spliceG i x y t u j= Maxwell.grad i (fun z=> Aster t u j (x-z)) y:= by
    unfold spliceG pull; have hh:= ((smoothA t u j (x-y) (sub_ne_zero.mpr hx)).differentiableAt (by simp)).hasFDerivAt; change - fderiv ℝ _ _ _= fderiv ℝ _ _ _;  rw [show fderiv ℝ (fun z=> Aster t u j (x-z)) y=_ from (hh.comp y ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))).fderiv]; simp

variable (hq:1<q.val)
include hq
lemma atlases : PS q i (transfer t u j) (Aster t u j) (pull i (Aster t u j)):= by
   have h:= transfer_air j u t; refine ⟨h,⟨h,fun {X Y x y} hx hy he=>?_⟩,⟨air_ds i h,fun {X Y x y} hx hy he=>?_⟩⟩; · let e(k:Axis):=cable q X Y 1 (graphS [k] 0); have h(k:Axis) : Tendsto (e k) L (𝓝 (Maxwell.grad k Green (x-y))) := cope hq he hx hy 0 [k]; refine (show Tendsto (fun j' => ∑ k:Axis, form t u k j * e k j') atTop _ from tendsto_finsetSum _ (fun i _=> (h i).const_mul _)).congr fun k=>?_ ; simp_rw [e,cable,sprite_val, transfer_val,Finset.mul_sum,mul_left_comm]
   let f(k:Axis):= -(cable q X Y 2 (graphS [i,k] (0-step i))); have hf(k:Axis): Tendsto (f k) L (𝓝 (-(Maxwell.grad i (Maxwell.grad k Green) (x-y)))):= (cope hq he hx hy _ [i,k]).neg
   rw [sized t u i j _ (sub_ne_zero.mpr he)]; refine (show Tendsto (fun j'=>∑ k:Axis,form t u k j * f k j') L _ from tendsto_finsetSum _ (fun i _=>(hf i).const_mul _)).congr fun k=>?_ ; simp_rw [cable,transfer, map_sum,map_smul,graph_d,sprite_val,Finset.sum_apply,Pi.smul_apply,Pi.neg_apply,smul_eq_mul]; simp only [f,Pi.neg_apply,cable,sprite_val,Finset.mul_sum,mul_neg,mul_left_comm,Finset.sum_neg_distrib]
end YM.PositionX.Chir.Dock
