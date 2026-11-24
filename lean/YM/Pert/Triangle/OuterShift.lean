import YM.Pert.Triangle.Ballistic
/-! Rescaled p-line error estimate outside the moving subtraction ball, with split integration in moving mark coordinates. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.Pert.Triangle
open Maxwell Analysis Set Function Metric Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace Classical
local notation "I3" => Fin 3
variable (i t:I3)
def cutoffbo (p : Bool) (x y w:E4) : Prop := if p then ‖w-x‖ ≤ ‖w-y‖ else ‖w-y‖ < ‖w-x‖
def born (p:Bool) (x y:E4) := if p then x else y
variable (a b:Axis)
def flowProduct (x y w:E4) := flow a (w-x) * flow b (w-y)
def crux (r:ℝ) (d x y w:E4) := (permitted i t r d x y w - mixed i t d) * flowProduct a b x y w
def firstSplit (p:Bool) (r:ℝ) (d x y w:E4) := ite (cutoffbo p x y w) (crux i t a b r d x y w) 0
lemma costingSplit {B:ℝ} (hB : 8 < B) : ∃ K>0, ∀ v w:E4, ‖v‖ ≤ B/2 → 1/2 ≤ ‖w+v‖ → ‖w‖ ≤ ‖w+v‖ → w≠0 →
     ‖flow a w * flow b (w+v)‖ ≤ capper B K w := by
    obtain ⟨K,hK,e⟩ := price (flow_rays a)
    obtain ⟨L,hL,h⟩ := price (flow_rays b)
    refine ⟨K*L,by positivity,fun v w hv hw hw' he=> ?_⟩
    rw [norm_mul,capper]
    split_ifs with h'
    · grw [e _ he, h _ (norm_pos_iff.mp (by linarith))]
      grw [←hw]
      field_simp; norm_num
    have := continues v w hB.le hv h'
    have hu : (1+‖w‖)/2 ≤ ‖w‖ := by rw [mem_closedBall_iff_norm,not_le,sub_zero] at h';linarith
    grw [e _ he, h _ (norm_pos_iff.mp (by linarith)),←hu,←this]
    rw [div_mul_div_comm]; field_simp; nlinarith

lemma splitAuto (p:Bool) (x y d:E4) (r:ℝ) : Measurable (firstSplit i t a b p r d x y) := by
  let f (v:E4) := fun w:E4=>w-v
  have hm (v:E4): Measurable (f v) := measurable_id.sub_const v
  have hp' : Measurable (permitted i t r d x y) := Measurable.ite isClosed_closedBall.measurableSet measurable_const (((rayMeasurable (mixed_rays i t)).comp (f:=fun w=>radial r d-w) (by fun_prop)).const_mul (r^4))
  have hf : Measurable (flowProduct a b x y) := ((rayMeasurable (flow_rays a)).comp (hm x)).mul ((rayMeasurable (flow_rays b)).comp (hm y))
  apply Measurable.ite (p:=fun w=>cutoffbo p x y w) ?_ ((hp'.sub_const _).mul hf) measurable_const
  cases p; exact measurableSet_lt (hm y).norm (hm x).norm; exact measurableSet_le (hm x).norm (hm y).norm
def spinned (p:Bool) (R:ℝ) (δ X Y u:E4):= firstSplit i t a b p R δ X Y (u+born p X Y)

lemma boundShape {B:ℝ} (hB:8 < B) (p:Bool) {C:ℝ} (hC : 0<C) : ∃ K>0, ∀ X Y R d u, ‖X‖≤B/4 → ‖Y‖ ≤ B/4 → 1 ≤ ‖X-Y‖ → u ≠ 0 →
     ‖spinned i t a b p R d X Y u‖ ≤ ‖permitted i t R d X Y (u+born p X Y)-mixed i t d‖ * capper B K u := by
   obtain ⟨K,hK,H⟩ := costingSplit a b hB
   obtain ⟨J,hJ,G⟩ := costingSplit b a hB
   refine ⟨K+J,by linarith,fun X Y R d u hx hy hxy hu=> ?_⟩
   have hc : ‖X-Y‖ ≤ B/2 := by linarith [norm_sub_le X Y]
   let M := ‖permitted i t R d X Y (u+born p X Y)-mixed i t d‖
   unfold spinned firstSplit
   change ‖ite _ _ _‖ ≤ M*capper B (K+J) u
   by_cases hw : cutoffbo p X Y (u+born p X Y)
   · rw [if_pos hw, crux,norm_mul]; gcongr
     unfold flowProduct
     have h'(L E:ℝ) (he:E≤L) : capper B E u ≤ capper B L u := by
        unfold capper;split_ifs with h
        · apply div_le_div_of_nonneg_right (by gcongr) (by positivity)
        exact div_le_div_of_nonneg_right (by gcongr) (by positivity)
     cases p
     · dsimp [cutoffbo,born] at hw ⊢; rw [show u+Y-X=u+(Y-X) by abel,add_sub_cancel_right] at *
       rw [mul_comm]
       have e : 1/2 ≤ ‖u+(Y-X)‖ := by
         have E1 := norm_add_le (Y-X+u) (-u)
         rw [add_neg_cancel_right, norm_sub_rev Y, norm_neg,add_comm (Y-X)] at E1
         linarith
       exact (G (Y-X) u ((norm_sub_rev Y X).trans_le hc) e hw.le hu).trans (h' _ _ (by linarith))
     · dsimp [cutoffbo,born] at hw ⊢
       rw [show u+X-Y=u+(X-Y) by abel,add_sub_cancel_right] at *
       have e : 1/2 ≤ ‖u+(X-Y)‖ := by
         have E1 := norm_add_le (X-Y+u) (-u)
         rw [add_neg_cancel_right, norm_neg,add_comm (X-Y)] at E1
         linarith
       exact (H (X-Y) u hc e hw hu).trans (h' _ _ (by linarith))
   exact if_neg hw ▸ by rw [norm_zero]; exact mul_nonneg (norm_nonneg _) (capperNonnegative _ (by linarith) _)

section
variable {R : ℕ→ℝ} (hR : Tendsto R atTop atTop) (p:Bool) {X Y δ:ℕ→E4} {x y d:E4}
   (hD : Tendsto δ atTop (𝓝 d)) (hU : ∀ n, ‖δ n‖=1) (hx : Tendsto X atTop (𝓝 x)) (hy : Tendsto Y atTop (𝓝 y))
variable (B:ℝ) (hB:8<B) (bx : ∀ k, ‖X k‖ ≤ B/4) (by' : ∀ k, ‖Y k‖ ≤ B/4) (bgap : ∀ k, 1 ≤ ‖X k-Y k‖)
include hR hD hU hx hy B hB bx by' bgap
lemma splitLimit : Tendsto (fun k=>∫ w, firstSplit i t a b p (R k) (δ k) (X k) (Y k) w) atTop (𝓝 0) := by
  let F k := spinned i t a b p (R k) (δ k) (X k) (Y k)
  obtain ⟨C,hC,hE⟩ := permitPrice i t
  obtain ⟨L,hL,quote⟩ := boundShape i t a b hB p hC
  have hm k : Measurable (F k) := (splitAuto i t a b p (X k) (Y k) _ _).comp (f:=fun u=>u+born p (X k) (Y k)) (measurable_id.add_const _)
  have hf : ∀ᶠ k in atTop, ∀ᵐ w ∂(volume : Measure E4), ‖F k w‖ ≤ C * capper B L w := by
     exact (hR.eventually (eventually_gt_atTop (2*B))).mono fun k hk=>(volume.ae_ne 0).mono fun v hv=> (quote _ _ _ _ _ (bx k) (by' k) (bgap k) hv).trans (mul_le_mul_of_nonneg_right (hE (B/4) _ _ _ _ (bx k) (by' k) (hU k) (by linarith) _) (capperNonnegative _ hL _))
  have hp (w:E4) (hw:w≠0) : Tendsto (fun k=>F k w) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have he : Tendsto (fun k=>w+born p (X k) (Y k)) atTop (𝓝 (w+born p x y)) := by cases p; exact tendsto_const_nhds.add hy;exact tendsto_const_nhds.add hx
    have hd : d≠0 := by rintro rfl; have e : ‖(0:E4)‖ = 1 := tendsto_nhds_unique hD.norm (by simp only [hU];exact tendsto_const_nhds); rw [norm_zero] at e; linarith
    have ht := permitLimit i t hR hD hU bx by' he |>.sub (((mixed_rays i t).diff hd).continuousAt.tendsto.comp hD)
    rw [sub_self] at ht
    apply squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) (Eventually.of_forall fun k=>quote _ _ _ _ _ (bx k) (by' k) (bgap k) hw) (by simpa using ht.norm.mul_const (capper B L w))
  have hi := tendsto_integral_filter_of_dominated_convergence (μ:=volume) (F:=F) (f:=fun _:E4=>(0:ℝ)) _ (Eventually.of_forall (fun k=>(hm k).aestronglyMeasurable)) hf ((capper_pay (by linarith) hL).const_mul C) ((volume.ae_ne 0).mono hp)
  simpa only [F,spinned,integral_add_right_eq_self, integral_zero] using hi
end
section mainRate
variable {R:ℕ→ℝ} (hR : Tendsto R atTop atTop) {X Y δ:ℕ→E4} {r x y d:E4}
    (hD : Tendsto δ atTop (𝓝 d)) (hU : ∀ n, ‖δ n‖=1) (hx:Tendsto X atTop (𝓝 x)) (hy : Tendsto Y atTop (𝓝 y))
    (B:ℝ) (hB:8<B) (bx : ∀ k, ‖X k‖ ≤ B/4) (by' : ∀ k, ‖Y k‖ ≤ B/4) (bgap : ∀ k, 1 ≤ ‖X k-Y k‖)
include hR hD hU hx hy B hB bx by' bgap
private lemma yclear (k) : X k ≠ Y k := fun e=>by have h := bgap k;rw [e, sub_self,norm_zero] at h; exact (not_lt.mpr h (by norm_num))
lemma payCrux (q : Axis) (k) (h:2*B < R k) :
    Integrable (crux i t a q (R k) (δ k) (X k) (Y k)) := by
    obtain ⟨C,hC,he⟩ := permitPrice i t
    have hp' : Measurable (permitted i t (R k) (δ k) (X k) (Y k)) := Measurable.ite isClosed_closedBall.measurableSet measurable_const (((rayMeasurable (mixed_rays i t)).comp (f:=fun w=>radial _ _-w) (by fun_prop)).const_mul _)
    exact (overlapPayable a q (yclear hR hD hU hx hy B hB bx by' bgap k)).bdd_mul (f:=fun v=>permitted i t (R k) (δ k) (X k) (Y k) v - _ ) (hp'.sub_const _).aestronglyMeasurable (ae_of_all _ (he (B/4) _ _ _ _ (bx k) (by' k) (hU k) (by linarith)))
lemma cruxLimit : Tendsto (fun k=>∫ w, crux i t a b (R k) (δ k) (X k) (Y k) w) atTop (𝓝 0) := by
  -- unnamed local t?
  have H (p) := splitLimit i t a b hR p hD hU hx hy B hB bx by' bgap
  rw [show (𝓝 (0:ℝ))=𝓝 (0+0)by simp]
  refine ((H true).add (H false)).congr' <| (hR.eventually (eventually_gt_atTop (2*B))).mono ?_
  intro k hk
  let f := crux i t a b (R k) (δ k) (X k) (Y k)
  let ht p := {u | cutoffbo p (X k) (Y k) u}
  have hm (p) : MeasurableSet (ht p) := by cases p
                                           exact measurableSet_lt (measurable_id.sub_const _ |>.norm) ((measurable_id.sub_const _).norm)
                                           exact measurableSet_le (measurable_id.sub_const _ |>.norm) ((measurable_id.sub_const _).norm)
  have hi p : Integrable (firstSplit i t a b p (R k) (δ k) (X k) (Y k)) volume := ((payCrux i t a hR hD hU hx hy B hB bx by' bgap b k hk).indicator (hm p))
  rw [← integral_add (hi _) (hi _)]
  congr 1; funext w; unfold firstSplit cutoffbo; by_cases h : ‖w-X k‖ ≤ ‖w-Y k‖ <;> simp [h,←not_le] at *

variable (m n : I3)
lemma priceCrux (k) (h:2*B < R k) :
    R k^4 * ∫ w,(outerZone i t m n (radial (R k) (δ k)) (X k) (Y k) w)
      = mixed i t (δ k) * (∫ w, integralInput t m n (X k) (Y k) w) + ∑ a, ∑ b, third m t n a b * ∫ w, crux i t a b (R k) (δ k) (X k) (Y k) w := by
  have he (a b:Axis) : Integrable (fun w : E4=> third m t n a b * crux i t a b (R k) (δ k) (X k) (Y k) w) := (payCrux i t a hR hD hU hx hy B hB bx by' bgap b k h).const_mul _
  simp_rw [←integral_const_mul]
  have innerEq (a):= integral_finsetSum Finset.univ (fun b _=>he a b)
  simp_rw [← innerEq]
  rw [←integral_finsetSum _ (fun a _=>integrable_finsetSum _ fun b _=>he a b)]
  rw [←integral_add]
  · apply integral_congr_ae (ae_of_all _ fun w:E4=> ?_)
    have eq : outerZone i t m n (radial (R k) (δ k)) (X k) (Y k) w = (if w∉zone (radial (R k) (δ k)) (X k) (Y k) then mixed i t (radial (R k) (δ k)-w) else 0) * integralInput t m n (X k) (Y k) w := by rw [ite_mul]; unfold outerZone; split_ifs <;> ring -- problematic underscores
    rw [eq]; split_ifs with hw
    all_goals
      simp only [input_expand,Finset.mul_sum,←Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _=>Finset.sum_congr rfl (fun b _=> ?_))
      unfold crux flowProduct permitted
    · rw [if_pos hw]; ring
    rw [if_neg hw];ring
  · exact (inputPayable t m n (yclear hR hD hU hx hy B hB bx by' bgap k)).const_mul _
  · exact integrable_finsetSum _ (fun a _=>integrable_finsetSum _ (fun b _=>he a b))
end mainRate
end YM.Pert.Triangle
