import YM.X.Chir.Harvest
/-!
# contraction identity.C orientation tilt scaled tensor. cofactor and determinant. point bubb.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity Imprint
open Maxwell (Green normal)
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R e c:ℝ}
local notation "L"=>(atTop:Filter ℕ)
local notation "ε"=> epsilon q
local notation "T"=> Tet
abbrev Arena:= Tet→Tet→ℝ
def Α (F G:Arena)(i u v:T):ℝ:= F (loop i) u* G (ℓ i) v-F (ℓ i) u*G (loop i) v
def detUp (f:Arena):= f 0 0* (f 1 1*f 2 2-f 2 1*f 1 2)-f 0 1*(f 1 0*f 2 2-f 2 0*f 1 2)+f 0 2*(f 1 0*f 2 1-f 2 0*f 1 1)
lemma pow_det (f:Arena)(a:ℝ): detUp (a • f)=a^3*detUp f:= by unfold detUp; simp only [Pi.smul_apply, smul_eq_mul]; ring
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8000 in
lemma rank_cube (f:Arena): ∑ i:T,∑ u:T,∑ v:T, Α f f i u v*(∑ j:T, f i j*η u j v)=(-6)*detUp f:= by
    have h0: loop 0=1:=rfl; have h1:loop 1=2:=rfl; have h2:loop 2=0:=rfl
    have h: (0:T)≠2:=by decide
    have hp : (1:T)≠2:=by decide
    norm_num [sum3,Α,η,ℓ,h0,h1,h2,detUp,h,hp,h.symm,hp.symm]; ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
lemma matrix_sp (x:E4): detUp (matrixU x)=-(‖x‖^2)^3:= by norm_num [detUp,matrixU,α_pair,sum4,form, EuclideanSpace.real_norm_sq_eq]; ring -- coord normal notation
lemma norm_spire (x:E4)(h:‖x‖=1): solar x= (8*normal) • matrixU x:= by ext1 p; ext1 t; simp [solar,h]
lemma coat_sun (x:E4)(h:‖x‖=1)(c:ℝ): ∑ i:T,∑ p:T,∑ v:T, Α (solar x) (solar x) i p v*(0-∑ u:T,solar x i u*(η p u v*c))=(-6)*(8*normal)^3*c:= by simp_rw [← mul_assoc (solar x _ _) (_:ℝ) c,← Finset.sum_mul _ _ c,zero_sub,mul_neg, ← mul_assoc (_:ℝ) _ c,Finset.sum_neg_distrib, ← Finset.sum_mul _ _ c]; rw [rank_cube,norm_spire x h,pow_det,matrix_sp,h]; ring
-- Hom scale estimates for leading T point.D
variable (p v t:Tet) (i:Axis) {x:E4}
local notation "U"=> matrixU
lemma tintU (a:ℝ): U (a • x) p t=a^2 * U x p t:= by simp_rw [matrixU, mul_neg, Finset.mul_sum]; apply congr_arg (- ·); apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [PiLp.smul_apply, PiLp.smul_apply]; change _* (a*_*(a*_))=_; ring
def Cup (p:T)(i:Axis) (x:E4):ℝ:= ∑ j:Axis, mn p j i *(-2 * normal * x j * (‖x‖^2)⁻¹^2)
lemma tint_s (a:ℝ)(ha:0<a)(x:E4): solar (a • x) p t=a⁻¹^4* solar x p t:= by unfold solar; rw [tintU,_root_.norm_smul, Real.norm_of_nonneg ha.le,mul_pow,mul_inv,mul_pow]; field_simp
lemma tilt_C (a:ℝ)(ha:0<a): Cup p i (a • x)=a⁻¹^3* Cup p i x:= by
    unfold Cup; rw [mul_sum]; apply sum_congr rfl; intro j _; rw [PiLp.smul_apply, norm_smul, Real.norm_of_nonneg ha.le,mul_pow,mul_inv,mul_pow]; rw [smul_eq_mul]; field_simp
lemma shine (h:x≠0): ContinuousAt (fun z=>solar z p t) x:= by
    have hx:‖x‖≠0:=(norm_pos_iff.mpr h).ne'; unfold solar matrixU; fun_prop (disch:= positivity) -- may fail
lemma cshine (h:x≠0): ContinuousAt (Cup p i) x:= by have hx: ‖x‖≠0:=(norm_pos_iff.mpr h).ne'; unfold Cup; fun_prop (disch:= positivity)
lemma urn {X Y: Fielding.Walk} (x y:E4)(h:x≠y)(hx:plot q X x)(hy:plot q Y y)(hq:1<q.val): Tendsto (fun k=>Wpv (ε k) (-1) p i (side q k) (transit q X k) (transit q Y k)) L (𝓝 (Cup p i (x-y))):= by
   simp_rw [w_c]; unfold Cup; refine tendsto_finsetSum _ (fun j _=>?_); rw [← Maxwell.first_Green (sub_ne_zero.mpr h) j]; exact (cope hq h hx hy 0 [j]).const_mul _
end YM.PositionX.Chir
