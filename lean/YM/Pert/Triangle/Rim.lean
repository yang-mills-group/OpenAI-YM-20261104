import YM.Pert.Triangle.Subtracted

/-! After scaling by fourth power of the distance to the bracket mark, the opposite-helicity p-line from the integration vertex has a diagonal limit in the region away from the moving subtraction ball. IR tail included. -/
set_option autoImplicit false
set_option maxHeartbeats 340000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Pert.Triangle
open Maxwell Analysis Set Metric Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace Classical
local notation "I3" => Fin 3
variable (x y : E4)

def outZ (R : ℝ) := R • along
def reachDistance := 1+4*‖x‖+4*‖y‖
lemma norm_out {R : ℝ} (h : reachDistance x y ≤ R) : ‖outZ R‖ = R := by
  have e := norm_nonneg x
  have e' := norm_nonneg y
  unfold reachDistance at h
  rw [outZ,norm_smul,Real.norm_eq_abs,along_norm,mul_one,abs_of_nonneg (by linarith : 0 ≤ R)]
lemma horizon {R : ℝ} (hf : reachDistance x y ≤ R) :
    0<R ∧ R/4 ≤ pairHole (outZ R) x y ∧ pairHole (outZ R) x y ≤ R*(5/8) := by
  have hx : ‖x‖ ≤ R/4 := by unfold reachDistance at hf; linarith [norm_nonneg x,norm_nonneg y]
  have hy : ‖y‖ ≤ R/4 := by unfold reachDistance at hf; linarith [norm_nonneg x,norm_nonneg y]
  have e : 0<R := by unfold reachDistance at hf; linarith [norm_nonneg x,norm_nonneg y]
  suffices he : R/2 ≤ min ‖outZ R-x‖ ‖outZ R-y‖ ∧ min ‖outZ R-x‖ ‖outZ R-y‖ ≤ 5*R/4 by
    exact ⟨e,(by unfold pairHole; linarith [he.1]),(by unfold pairHole; linarith [he.2])⟩
  have z := norm_out x y hf
  exact ⟨le_min (by linarith [norm_sub_norm_le (outZ R) x]) (by linarith [norm_sub_norm_le (outZ R) y]), (min_le_left ..).trans (by linarith [norm_sub_le (outZ R) x])⟩
lemma eventuallyOuter (w : E4) : ∀ᶠ R : ℝ in atTop, w ∉ zone (outZ R) x y := by
  filter_upwards [eventually_ge_atTop (reachDistance x y),eventually_gt_atTop (8*‖w‖)] with R hR hdist hw
  have hh := (horizon x y hR).2.2
  have := norm_nonneg w
  have he := calc
    R = ‖outZ R‖ := (norm_out x y hR).symm
    _ ≤ ‖outZ R-w+w‖ := by rw [sub_add_cancel]
    _ ≤ ‖outZ R-w‖ + ‖w‖ := norm_add_le ..
    _ ≤ pairHole (outZ R) x y + ‖w‖ := by grw [norm_sub_rev _ w, mem_closedBall_iff_norm.mp hw]
  linarith
variable (i t : I3)
include x y in
lemma explode (w : E4) {R} (he : reachDistance x y ≤ R) (hr : w ∉ zone (outZ R) x y) :
    (outZ R-w) ≠ 0 ∧ ∀ C:ℝ, 0<C → ‖mixed i t (outZ R-w)‖ ≤ C / ‖outZ R-w‖^4 → R^4 * ‖mixed i t (outZ R-w)‖ ≤ 4^4*C := by
  have h : R/4 ≤ ‖outZ R-w‖ := (horizon x y he).2.1.trans (le_of_not_ge (fun e : _ => hr (mem_closedBall_iff_norm.mpr ((norm_sub_rev _ w) ▸ e)))) -- wrong
  have hR := (horizon x y he).1
  have hw : outZ R - w ≠ 0 := norm_pos_iff.mp (by linarith)
  refine ⟨hw,?_⟩
  intro C hC hc
  grw [hc]
  rw [mul_div_assoc',div_le_iff₀ (by positivity)]
  calc R^4 * C ≤ (4*‖outZ R-w‖)^4*C := by gcongr; linarith
       _ = 4^4 * C * ‖outZ R-w‖^4 := by ring
include x y in
lemma transported (w : E4) {R} (he : reachDistance x y ≤ R) (hr : w ∉ zone (outZ R) x y) :
    R^4 * mixed i t (outZ R-w) = mixed i t (along - R⁻¹ • w) := by
  have hR := (horizon x y he).1
  have ha : R • (along-R⁻¹ • w) = outZ R-w := by rw [smul_sub,smul_inv_smul₀ hR.ne'];rfl
  have hw := explode x y i t w he hr |>.1
  rw [←ha]
  exact (mixed_rays i t).stretch (fun e=> hw (by rw [←ha,e,smul_zero])) hR.ne'
-- in event methods retain actual constants
variable (m n : I3)
def inflated (R : ℝ) (w : E4) := R^4 * outerZone i t m n (outZ R) x y w
lemma inflateBound : ∃ L>0, ∀ᶠ R in atTop, ∀ w, ‖inflated x y i t m n R w‖ ≤ L * ‖integralInput t m n x y w‖ := by
  obtain ⟨D,hD,hd⟩ := price (mixed_rays i t)
  refine ⟨4^4*D,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (reachDistance x y)] with R hR w
  unfold inflated outerZone
  split_ifs with h
  · rw [mul_zero,norm_zero]
    positivity
  have hw := explode x y i t w hR h
  rw [norm_mul,Real.norm_of_nonneg (by positivity),norm_mul,←mul_assoc]
  exact mul_le_mul_of_nonneg_right (hw.2 D hD (hd _ hw.1)) (norm_nonneg _)
lemma inflatePoint (w : E4) : Tendsto (inflated x y i t m n · w) atTop (𝓝 (mixed i t along * integralInput t m n x y w)) := by
  have ht : Tendsto (fun R : ℝ=>along-(R⁻¹ • w)) atTop (𝓝 along) := (by simpa using (Filter.Tendsto.sub (f:=fun _:ℝ=>along) tendsto_const_nhds (tendsto_inv_atTop_zero.smul_const w)))
  have hi := ((mixed_rays i t).diff along_zero).continuousAt.tendsto.comp ht
  refine hi.mul_const _ |>.congr' ?_
  filter_upwards [eventuallyOuter x y w, eventually_ge_atTop (reachDistance x y)] with R hr he
  rw [inflated,outerZone,if_pos hr,← mul_assoc,transported x y i t w he hr]
  rfl
lemma inflateLimit (h : x ≠ y) : Tendsto (fun R => R^4 * ∫ w, outerZone i t m n (outZ R) x y w) atTop (𝓝 ((if i=t then -4*normal else 0) * ∫ w, integralInput t m n x y w)) := by
  obtain ⟨L, hL, H⟩ := inflateBound x y i t m n
  have he := tendsto_integral_filter_of_dominated_convergence (μ:=volume) (F:=inflated x y i t m n) _ (Eventually.of_forall fun _=> (Measurable.const_mul (outerMeasurable ..) _).aestronglyMeasurable) (H.mono (fun R h=>ae_of_all _ h)) ((inputPayable t m n h).norm.const_mul _) (ae_of_all volume (inflatePoint x y i t m n))
  exact (by simpa only [integral_const_mul,mixed_diagonal,inflated] using he)
end YM.Pert.Triangle
