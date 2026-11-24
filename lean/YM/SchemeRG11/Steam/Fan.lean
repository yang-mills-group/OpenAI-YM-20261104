import YM.SchemeRG11.Steam.Snap
import YM.Pert.Triangle.Estimate
/-!
Only now d4 contractions with chiral tensors. Mixed heat lines have shell cancellation.
-/
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
namespace YM.SchemeRG11.Steam
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter Cluster MSbar Pert Triangle
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace

def edge (h : Bool) (i : Eye) (a : Axis) (x : E4) := ∑ b,fan h i b a * score [b] x
/-- mark FIRST: x=x_mark-x_A. -/
def wing (h : Bool) (i : Eye) (a : Axis) (t : ℝ) (x : E4) := ∑ b,fan h i b a * tint [b] t x
/-- both curls, d4 only. -/
def fused (hi : Bool) (i : Eye) (hj : Bool) (j : Eye) (t : ℝ) (x : E4) := -(∑ a,∑ c,tint [a,c] t x * rotatedProduct hi i hj j a c)
lemma dusk (h : Bool) (i j : Eye) (x : E4) (t : ℝ) :
    fused h i h j t x = - ((2:ℝ)⁻¹ * if i=j then ∑ a,tint [a,a] t x else 0) := by
  have hh (a c : Axis) : tint [c,a] t x=tint [a,c] t x:= by rw [second_line,second_line]; simp [basis_eq,eq_comm,mul_comm]
  have he:= pays_trace (fun a c=>tint [a,c] t x) hh h i j
  unfold fused; linarith

lemma edge_minus (i:Eye)(a:Axis)(x:E4): edge false i a (-x)= mLine i a x:=by
  unfold edge mLine; apply Finset.sum_congr rfl; intro b hb
  change _*grad b Maxwell.Green (-x)=_
  rw [show grad b Maxwell.Green (-x)=-flow b (-x) from by rw [flow,neg_neg],flow_odd,neg_neg]
lemma wings_pay (h : Bool) (i : Eye) (a : Axis) {x:E4} (hx:x≠0) : IntegrableOn (fun t=>wing h i a t x) openZen:= integrable_finsetSum _ (fun b _=> (tint_i [b] hx).const_mul _)
lemma edges (h : Bool) (i : Eye) (a : Axis) {x:E4} (hx:x≠0) : edge h i a x=∫ t in openZen, wing h i a t x := by
 unfold edge wing; rw [integral_finsetSum _ (fun a _=> (tint_i [_] hx).const_mul _)]; simp only [integral_const_mul,sculpt _ _ hx]; rfl
lemma fuse_pay (hi : Bool) (i : Eye) (hj : Bool) (j : Eye) {x:E4} (hx:x≠0) : IntegrableOn (fun t=>fused hi i hj j t x) openZen:= (integrable_finsetSum _ (fun a _=> integrable_finsetSum _ fun b _=> (tint_i [a,b] hx).mul_const _)).neg

lemma mixed_heat (i j : Eye) {x:E4} (hx:x≠0) : mixed i j x=∫ t in openZen, fused true i false j t x := by
  simp only [mixed_contact i j hx,fused,integral_neg]; congr 1
  rw [integral_finsetSum _ (fun a _=> integrable_finsetSum _ (fun c _=> (tint_i [a,c] hx).mul_const _))]
  unfold tensorSum; apply Finset.sum_congr rfl; intro a _; rw [integral_finsetSum _ (fun c _=> (tint_i [a,c] hx).mul_const _)]; simp only [integral_mul_const,sculpt _ _ hx]; rfl

lemma wing_position (h:Bool) (i : Eye) (a : Axis) (t : ℝ) : ContDiff ℝ ∞ (wing h i a t) := ContDiff.sum fun b _=> contDiff_const.mul (series_calm (gauze_diff t) [basis b])
lemma fuse_position (hi:Bool)(i:Eye)(hj:Bool)(j:Eye)(t:ℝ): ContDiff ℝ ∞ (fused hi i hj j t) := (ContDiff.sum fun a _=> ContDiff.sum fun b _=> (series_calm (gauze_diff t) [basis a,basis b]).mul contDiff_const).neg

/-- Pointwise time integrals of absolute values, not global. -/
lemma wing_pays (hi : Bool) (i : Eye) (a : Axis) : ∃ C>0, ∀ x:E4,x≠0 →
    (∫ t in openZen,‖wing hi i a t x‖) ≤ C/‖x‖^3 := by
  choose C hC h using fun b=> income [b]
  let D:= ∑ b,‖fan hi i b a‖ * C b
  refine ⟨1+D,by apply add_pos_of_pos_of_nonneg zero_lt_one; exact Finset.sum_nonneg (fun b _=> mul_nonneg (norm_nonneg _) (hC b).le),fun x hx=>?_⟩
  let f:= fun t:ℝ=>∑ b,‖fan hi i b a‖*‖tint [b] t x‖
  refine (setIntegral_mono_on (wings_pay hi i a hx|>.norm) (g:=f) (integrable_finsetSum _ (fun b _=> (tint_i [b] hx|>.norm).const_mul _)) measurableSet_Ioi (fun p hp=> ?_)).trans ?_
  · refine (norm_sum_le ..).trans ?_; unfold f; simp only [norm_mul]; exact le_rfl
  unfold f; rw [integral_finsetSum _ (fun b _=> (tint_i [b] hx|>.norm).const_mul _)]
  simp only [integral_const_mul]; refine le_trans ?_ (div_le_div_of_nonneg_right (by linarith : D≤1+D) (by positivity)); unfold D; rw [Finset.sum_div]
  exact Finset.sum_le_sum (fun b _=> (mul_le_mul_of_nonneg_left (h b x hx) (norm_nonneg _)).trans_eq (by simp [mul_div_assoc]))
lemma fuse_pays (hi : Bool)(i : Eye)(hj : Bool)(j : Eye) : ∃ C>0, ∀ x:E4,x≠0 →
    (∫ t in openZen, ‖fused hi i hj j t x‖) ≤ C/‖x‖^4 := by
  choose C hC h using fun a b=> income [a,b]; let f:=rotatedProduct hi i hj j
  let D:=∑ a,∑ b,C a b*‖f a b‖
  refine ⟨1+D,by apply add_pos_of_pos_of_nonneg zero_lt_one; exact Finset.sum_nonneg fun i _=> Finset.sum_nonneg (fun j _=> mul_nonneg (hC i j).le (norm_nonneg _)),fun x hx=>?_⟩
  let v := fun a (t:ℝ)=>∑ b,‖tint [a,b] t x‖*‖f a b‖
  have he a : IntegrableOn (v a) openZen := integrable_finsetSum _ (fun b _=> (tint_i [a,b] hx|>.norm).mul_const _)
  refine (setIntegral_mono_on (fuse_pay hi i hj j hx|>.norm) (g:=fun t=>∑ a,v a t) (integrable_finsetSum _ (fun a _=> he a)) measurableSet_Ioi (fun p hp=> ?_)).trans ?_
  · unfold fused; rw [norm_neg]; exact (norm_sum_le ..).trans (Finset.sum_le_sum (fun a _=> (norm_sum_le ..).trans (by simp only [v,f,norm_mul]; exact le_rfl)))
  rw [integral_finsetSum _ (fun a _=> he a)]; refine le_trans ?_ (div_le_div_of_nonneg_right (by linarith : D≤1+D) (by positivity))
  unfold D; rw [Finset.sum_div]; apply Finset.sum_le_sum; intro a _; unfold v; rw [integral_finsetSum _ (fun b _=> (tint_i [a,b] hx|>.norm).mul_const _), Finset.sum_div]; simp only [integral_mul_const]; apply Finset.sum_le_sum; intro b _; exact (mul_le_mul_of_nonneg_right (h a b x hx) (norm_nonneg _)).trans_eq (by simp [div_mul_eq_mul_div])
end YM.SchemeRG11.Steam
