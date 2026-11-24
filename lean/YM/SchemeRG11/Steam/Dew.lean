import YM.SchemeRG11.Steam.Fan
/-!
Zero mix on a whole ball. Fixed positive time, no principal value.
-/
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.SchemeRG11.Steam
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter Cluster MSbar Pert Triangle
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace
variable (i j : Eye) (t R : ℝ)
local notation "K" => closedBall (0:E4) R

def mat (v u : E4) := ∫ w:E4 in K, inner ℝ v w * inner ℝ u w * gauze t w
lemma mat_entry (v u : E4) : IntegrableOn (fun w:E4=> inner ℝ v w * inner ℝ u w * gauze t w) K := by
  exact ((continuous_const.inner continuous_id).mul (continuous_const.inner continuous_id)|>.mul (gauze_diff t).continuous).continuousOn.integrableOn_compact (isCompact_closedBall ..)
lemma mat_sym (v u : E4) : mat t R v u=mat t R u v:= by
  unfold mat; refine integral_congr_ae (Eventually.of_forall fun w=>?_); dsimp only; rw [mul_comm (inner ℝ v w)]
lemma mat_add (a b c : E4) : mat t R (a+b) c=mat t R a c+mat t R b c:= by simp only [mat,inner_add_left,add_mul]; rw [integral_add (mat_entry ..) (mat_entry ..)]
lemma mat_sub (a b c : E4) : mat t R (a-b) c=mat t R a c-mat t R b c:= by simp only [mat,inner_sub_left,sub_mul]; rw [integral_sub (mat_entry ..) (mat_entry ..)]
lemma mat_tot (a b : E4) (h : ‖a‖=‖b‖) : mat t R a a= mat t R b b:= by
  let M := Submodule.reflection (ℝ ∙ (a-b))ᗮ
  have he : M a=b := Submodule.reflection_sub h
  let V:Measure E4:=volume
  have hz : MeasurePreserving M (V.restrict (M ⁻¹' K)) (V.restrict K) := M.measurePreserving.restrict_preimage_emb M.toHomeomorph.measurableEmbedding _
  rw [show M ⁻¹' K=K by ext; simp] at hz
  have ht:= hz.integral_comp M.toHomeomorph.measurableEmbedding (fun w=> inner ℝ b w * inner ℝ b w * gauze t w)
  rw [mat,mat,← ht]
  refine integral_congr_ae (Eventually.of_forall fun w=>?_); dsimp only; rw [←he, M.inner_map_map]; unfold gauze; rw [M.norm_map]
lemma mat_hom (a b : Axis) : mat t R (basis a) (basis b)= if a=b then mat t R (basis 0) (basis 0) else 0 := by
  split
  next h => subst b; exact mat_tot _ _ _ _ (by simp)
  next h =>
    have hh:=mat_tot t R (basis a+basis b) (basis a-basis b) (by
      apply sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp; simp only [← real_inner_self_eq_norm_sq,inner_add_left,inner_sub_left,inner_add_right,inner_sub_right,basis_inner,basis_eq,eq_self,if_true,if_neg h,if_neg (Ne.symm h)]; ring)
    rw [mat_add,mat_sym t R (basis a),mat_add, mat_sym t R (basis b) (_+_),mat_add, mat_sub, mat_sym t R (basis a) (_-_ : E4), mat_sub,mat_sym t R (basis b) (_-_ : E4), mat_sub,mat_sym t R (basis b) (basis a)] at hh
    linarith

lemma aisle (a b : Axis) : (∫ x in K, tint [a,b] t x)=
    if a=b then -(2*α t)*(∫ x in K,gauze t x)+(2*α t)^2*mat t R (basis 0) (basis 0) else 0 := by
  have he x : tint [a,b] t x = -(2 * α t) * basis a b * gauze t x + (2*α t)^2 * (inner ℝ (basis a) x* inner ℝ (basis b) x*gauze t x) := by rw [second_line,basis_inner,basis_inner]; ring
  have hp : IntegrableOn (gauze t) K := (gauze_diff t).continuous.continuousOn.integrableOn_compact (isCompact_closedBall ..)
  simp_rw [he]; rw [integral_add (hp.const_mul _) ((mat_entry t R (basis a) (basis b)).const_mul _), integral_const_mul,integral_const_mul, ← mat,mat_hom]
  by_cases h:a=b <;> simp [h,eq_comm]

lemma dusty : (∫ x in K,fused true i false j t x)=0 := by
  have hi (a : Axis) : IntegrableOn (fun x:E4=>∑ c,tint [a,c] t x * rotatedProduct true i false j a c) K := by
     refine integrable_finsetSum _ (fun b _=>?_); exact ((series_calm (gauze_diff t) [basis a,basis b]).continuous.continuousOn.integrableOn_compact (isCompact_closedBall ..)).mul_const _
  unfold fused; rw [integral_neg,integral_finsetSum _ (fun a _=> hi a)]
  have hh a : (∫ x:E4 in K, ∑ c : Axis, tint [a,c] t x* rawProduct i j a c)= ∑ c, (∫ x in K,tint [a,c] t x)*rawProduct i j a c:= by
    rw [integral_finsetSum]; · simp only [integral_mul_const]
    exact fun c _=> ((series_calm (gauze_diff t) [basis a,basis c]).continuous.continuousOn.integrableOn_compact (isCompact_closedBall ..)).mul_const _
  change -(∑ a:Axis,∫ x in K, ∑ c : Axis,tint [a,c] t x*rawProduct i j a c)=_
  simp only [hh,aisle t R,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true, ← Finset.mul_sum,trace_rule,mul_zero,neg_zero]

lemma keys (z:E4) : (∫ x in closedBall z R,fused true i false j t (z-x))=0 := by
  let D:= fused true i false j t
  have he x : (K).indicator D (z-x)=(closedBall z R).indicator (fun x=> D (z-x)) x := by
     by_cases h:x∈closedBall z R
     · rw [indicator_of_mem h,indicator_of_mem]; simpa only [mem_closedBall_iff_norm,sub_zero,norm_sub_rev z x] using h
     rw [indicator_of_notMem h,indicator_of_notMem]; simpa only [mem_closedBall_iff_norm,sub_zero,norm_sub_rev z x] using h
  change (∫ x in closedBall z R,D (z-x))=_
  rw [← integral_indicator (f:=fun x=>D (z-x)) isClosed_closedBall.measurableSet]; simp_rw [← he]
  rw [integral_sub_left_eq_self,integral_indicator isClosed_closedBall.measurableSet]
  exact dusty i j t R
end YM.SchemeRG11.Steam
