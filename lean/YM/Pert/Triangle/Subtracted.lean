import YM.Pert.Triangle.Price
/-!
The opposite-helicity single curl-to-curl line used with a local *value* subtraction;
the second-order Green derivative singularity then multiplies an O(distance) difference.
This is only for the reduced two-`U` triangle integral, not a rule for
multi-subgraph renormalization or identification with finite-lattice coefficients.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Pert.Triangle
open Maxwell Analysis Set Metric Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace Classical
local notation "I3" => Fin 3

def pairHole (z x y : E4) := (min ‖z-x‖ ‖z-y‖)/2
def zone (z x y : E4) := closedBall z (pairHole z x y)
lemma zone_separated {z x y w : E4} (hx : z ≠ x) (hy : z ≠ y) (hw : w ∈ zone z x y) :
    w ≠ x ∧ w ≠ y := by
  rw [zone,mem_closedBall_iff_norm] at hw
  unfold pairHole at hw
  exact ⟨fun hr=>by
    subst w
    rw [norm_sub_rev x z] at hw
    exact (not_le_of_gt (half_lt_self (norm_pos_iff.mpr (sub_ne_zero.mpr hx)))) (hw.trans (by grw [min_le_left])),
    fun he=>by
      subst w
      rw [norm_sub_rev y z] at hw
      exact (not_le_of_gt (half_lt_self (norm_pos_iff.mpr (sub_ne_zero.mpr hy)))) (hw.trans (by grw [min_le_right]))⟩
lemma zone_self (z x y : E4) : z ∈ zone z x y := mem_closedBall_self (show 0 ≤ min _ _/2 by positivity)
variable (i t m n : I3) (z x y : E4)
def innerZone (w : E4) := if w ∈ zone z x y then mixed i t (z-w) * (integralInput t m n x y w - integralInput t m n x y z) else 0
def outerZone (w : E4) := if w ∉ zone z x y then mixed i t (z-w) * integralInput t m n x y w else 0
def against := (∫ w, innerZone i t m n z x y w)+(∫ w,outerZone i t m n z x y w)
lemma mLine_regular (a : Axis) {u:E4} (hu : u≠0) : ContDiffAt ℝ ∞ (mLine m a) u := by
  unfold mLine; exact ContDiffAt.sum (fun b _=> contDiffAt_const.mul (flow_rays b |>.diff hu))
lemma factor_regular {w} (hx : w ≠ x) (hy : w ≠ y) : ContDiffAt ℝ ∞ (integralInput t m n x y) w := by
  have hr (z : E4) (a : Axis) (k) (he : w ≠ z) : ContDiffAt ℝ ∞ ((mLine k a) ∘ (fun x:E4=>x-z)) w := by
    exact ContDiffAt.comp (g:=mLine k a) (f:=fun x:E4=>x-z) w (mLine_regular _ _ (sub_ne_zero.mpr he)) (contDiffAt_id.sub contDiffAt_const)
  unfold integralInput
  exact ContDiffAt.sum (fun _ _=> ContDiffAt.sum (fun b _=> (contDiffAt_const.mul (hr x _ _ hx) |>.mul (hr y _ _ hy))))
lemma factor_measurable : Measurable (integralInput t m n x y) := by
  rw [show integralInput t m n x y = _ from funext (input_expand t m n x y)]
  refine Finset.measurable_sum Finset.univ (fun a _=> Finset.measurable_sum Finset.univ (fun b _=>(Measurable.mul measurable_const <| (Measurable.comp (g:=flow a) (rayMeasurable (flow_rays a)) (measurable_id.sub_const _)).mul (Measurable.comp (g:=flow b) (rayMeasurable (flow_rays b)) (measurable_id.sub_const _)))))
lemma innerSize (hx : z≠x) (hy : z≠y) : ∃ C>0, ∀ w, w ≠ z → ‖innerZone i t m n z x y w‖ ≤ C / ‖w-z‖^3 := by
  obtain ⟨L,hL,he⟩ := price (mixed_rays i t)
  let f := integralInput t m n x y
  let K := zone z x y
  have hp : IsCompact K := isCompact_closedBall ..
  have hr (u) (hu : u ∈ K) := factor_regular t m n x y (zone_separated hx hy hu).1 (zone_separated hx hy hu).2
  obtain ⟨A,hA⟩ := hp.exists_bound_of_continuousOn (f:=fderiv ℝ f) (fun w hw=> (hr w hw |>.continuousAt_fderiv (by decide)).continuousWithinAt)
  refine ⟨L*(|A|+1),by positivity,fun w hw=>?_⟩
  by_cases e : w∈K
  · have h := norm_pos_iff.mpr (sub_ne_zero.mpr hw)
    have hLip := (convex_closedBall z (pairHole z x y)).norm_image_sub_le_of_norm_fderiv_le (x:=z) (y:=w) (𝕜:=ℝ) (fun w hw=>hr w hw |>.differentiableAt (by decide)) hA (zone_self z x y) e
    rw [innerZone,if_pos e,norm_mul]
    change _ * ‖f w - f z‖ ≤ _
    apply mul_le_mul (he (z-w) (sub_ne_zero.mpr hw.symm)) hLip (norm_nonneg _) (by positivity) |>.trans
    rw [norm_sub_rev z w]
    field_simp
    exact (le_abs_self A).trans (by linarith)
  rw [innerZone,if_neg e,norm_zero]; positivity
lemma innerMeasurable : Measurable (innerZone i t m n z x y) := Measurable.ite isClosed_closedBall.measurableSet (
    ((rayMeasurable (mixed_rays i t)).comp (f:=fun w:E4=>z-w) (measurable_const.sub measurable_id)).mul ((factor_measurable t m n x y).sub measurable_const))
    measurable_const -- no IsClosed method
lemma outerMeasurable : Measurable (outerZone i t m n z x y) := Measurable.ite (isClosed_closedBall.measurableSet.compl) (
    ((rayMeasurable (mixed_rays i t)).comp (f:=fun w:E4=>z-w) (measurable_const.sub measurable_id)).mul (factor_measurable t m n x y)) measurable_const
lemma innerPay (hx : z≠x) (hy : z≠y) : Integrable (innerZone i t m n z x y) := by
  let g := innerZone i t m n z x y
  let r := pairHole z x y
  let s := closedBall (0:E4) r
  let f := fun v=>g (v+z)
  obtain ⟨L,hL,he⟩ := innerSize i t m n z x y hx hy
  have hi := (locallyIntegrable_of_norm_le_rpow (α:=(3:ℕ)) (μ:=volume) (f:=f) (C:=L)
    (by rw [four_rank];decide) (by rw [four_rank];norm_num) ((volume.ae_ne 0).mono (fun v hv=>by rw [inv_power,← div_eq_mul_inv]; simpa only [add_sub_cancel_right] using he (v+z) (fun h=>hv (add_eq_right.mp h)))) ((innerMeasurable i t m n z x y).comp (measurable_id.add_const z)).aestronglyMeasurable).integrableOn_isCompact (isCompact_closedBall (0:E4) r)
  have hr (w) (hw : w∈sᶜ) : f w=0 := by
    change w∉s at hw
    change innerZone i t m n z x y (w+z)=0
    rw [innerZone,if_neg]
    exact fun h=> hw (by simpa only [s,r,zone,mem_closedBall_iff_norm,sub_zero,add_sub_cancel_right] using h)
  suffices h : Integrable f volume by simpa only [f,sub_add_cancel] using h.comp_sub_right z
  have hm : MeasurableSet sᶜ := isClosed_closedBall.measurableSet.compl
  change IntegrableOn f s volume at hi
  exact integrableOn_univ.mp (by simpa only [Set.union_compl_self] using hi.union ((integrableOn_congr_fun_ae (g:=fun _:E4=>(0:ℝ)) (μ:=volume) (s:=sᶜ) ((ae_restrict_of_forall_mem hm hr))).mpr (by simp)))
lemma outerPay (hx : z≠x) (hy:z≠y) (h:x≠y) : Integrable (outerZone i t m n z x y) := by
  let r := pairHole z x y
  obtain ⟨L,hL,he⟩ := price (mixed_rays i t)
  have hp : 0<r := half_pos (lt_min (norm_pos_iff.mpr (sub_ne_zero.mpr hx)) (norm_pos_iff.mpr (sub_ne_zero.mpr hy)))
  have hd (w) : ‖outerZone i t m n z x y w‖ ≤ (L / r^4) * ‖integralInput t m n x y w‖ := by
    unfold outerZone
    by_cases hk : w ∈ zone z x y
    · rw [if_neg (not_not.mpr hk), norm_zero]; positivity
    rw [if_pos hk,norm_mul]
    have hw : r < ‖z-w‖ := by rw [norm_sub_rev]; exact lt_of_not_ge (fun q=> hk (mem_closedBall_iff_norm.mpr q))
    exact mul_le_mul_of_nonneg_right ((he _ (norm_pos_iff.mp (hp.trans hw))).trans (by gcongr)) (by positivity)
  exact Integrable.mono' ((inputPayable t m n h).norm.const_mul _) (outerMeasurable i t m n z x y).aestronglyMeasurable (ae_of_all _ hd)
end YM.Pert.Triangle
