import YM.Pert.Triangle.Rim
/-! UV-subtracted contribution on the moving ball about the distant bracket mark. At order of the rescaled mixed p line this vanishes (pay the ball in its own units, not by a coincident point evaluation). -/
set_option autoImplicit false
set_option maxHeartbeats 340000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Pert.Triangle
open Maxwell Analysis Set Metric Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace Classical
local notation "I3" => Fin 3
variable (x y : E4) (i t m n:I3)
lemma flow_energy (a:Axis) {r:ℝ} {z:E4} (hr : r≠0) (hz:z≠0) : r^3 * flow a (r • z)=flow a z := (flow_rays a).stretch hz hr
lemma input_energy {r : ℝ} (hr : r≠0) (w : E4) (hx : w≠x) (hy:w≠y) : r^6 * integralInput t m n (r•x) (r•y) (r•w) = integralInput t m n x y w := by
  simp_rw [input_expand,←smul_sub,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  exact Finset.sum_congr rfl (fun b _=> by rw [show ∀ u p q : ℝ, r^6*(u*(p*q)) = u * ((r^3*p)*(r^3*q)) from fun _ _ _=>by ring,flow_energy a hr (sub_ne_zero.mpr hx),flow_energy b hr (sub_ne_zero.mpr hy)])

def small : Set E4 := closedBall 0 (1/4)
def stage : Set E4 := closedBall along (5/8)
@[simp] lemma small_compact : IsCompact small := isCompact_closedBall ..
@[simp] lemma stage_compact : IsCompact stage := isCompact_closedBall ..
lemma small_reset {R : ℝ} (h : reachDistance x y ≤ R) : R⁻¹ • x ∈ small ∧ R⁻¹ • y ∈ small := by
  have hR := (horizon x y h).1
  simp_rw [small,mem_closedBall_iff_norm,sub_zero,norm_smul,Real.norm_of_nonneg (inv_nonneg_of_nonneg hR.le), inv_mul_le_iff₀ hR]
  unfold reachDistance at h
  exact ⟨by linarith [norm_nonneg x, norm_nonneg y],by linarith [norm_nonneg x,norm_nonneg y]⟩
lemma apart {u v:E4} (hu : u∈stage) (hv:v ∈small) : u≠v := by
  rintro rfl
  simp only [stage,mem_closedBall_iff_norm] at hu
  simp only [small,mem_closedBall_iff_norm,sub_zero] at hv
  have := norm_sub_le u (u-along)
  rw [show u-(u-along)=along by abel,along_norm] at this -- name?
  linarith
lemma stage_self : along∈stage := mem_closedBall_self (by norm_num : (0:ℝ) ≤ 5/8)
include x y in
lemma restaged {u : E4} {R : ℝ} (h : reachDistance x y ≤ R) (hr : R • u ∈ zone (outZ R) x y) : u∈stage := by
  rw [zone,mem_closedBall_iff_norm,outZ,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (horizon x y h).1.le] at hr
  exact mem_closedBall_iff_norm.mpr ((mul_le_mul_iff_right₀ (horizon x y h).1).mp (hr.trans (horizon x y h).2.2))

lemma boundedSlope : ∃ M>0, ∀ x∈small,∀ y∈small,∀ v∈stage,∀ w∈stage, ‖integralInput t m n x y v - integralInput t m n x y w‖ ≤ M * ‖v-w‖ := by
  let f := fun z : E4 × E4 × E4 => integralInput t m n z.1 z.2.1 z.2.2
  let A := small ×ˢ small ×ˢ stage
  have hA : IsCompact A := small_compact.prod (small_compact.prod stage_compact)
  have hcont (z) (hz : z∈A) : ContDiffAt ℝ 1 f z := by
     have hi : z.2.2-z.1 ≠ 0 := sub_ne_zero.mpr (apart hz.2.2 hz.1)
     have hj : z.2.2-z.2.1 ≠ 0 := sub_ne_zero.mpr (apart hz.2.2 hz.2.1)
     unfold f integralInput
     refine ContDiffAt.sum (fun a _=> ContDiffAt.sum fun b _=> ?_)
     refine (contDiffAt_const.mul ?_).mul ?_
     · apply ContDiffAt.comp (g:=mLine m a) (f:=fun z : E4 × E4 × E4 => z.2.2-z.1) _ ((mLine_regular m a hi).of_le (by decide))
       apply ContDiffAt.sub <;> fun_prop
     apply ContDiffAt.comp (g:=mLine n b) (f:=fun z : E4 × E4 × E4 => z.2.2-z.2.1) _ ((mLine_regular n b hj).of_le (by decide))
     apply ContDiffAt.sub <;> fun_prop
  obtain ⟨D,hD⟩ := hA.exists_bound_of_continuousOn (f:=fderiv ℝ f) (fun v hv=> (hcont v hv |>.continuousAt_fderiv (by decide)).continuousWithinAt)
  refine ⟨|D|+1,by positivity,fun x hx y hy v hv w hw=>?_⟩
  have hcx : Convex ℝ A := Convex.prod (convex_closedBall ..) (Convex.prod (convex_closedBall ..) (convex_closedBall ..))
  have he := hcx.norm_image_sub_le_of_norm_fderiv_le (x:=(x,y,w)) (y:=(x,y,v)) (𝕜:=ℝ) (fun z hz=>(hcont z hz).differentiableAt (by decide)) hD ⟨hx,hy,hw⟩ ⟨hx,hy,hv⟩
  simpa [f,-ge_iff_le] using (show _ ≤ (|D|+1) * ‖(x,y,v) - (x,y,w)‖ from he.trans (by gcongr; exact (le_abs_self _).trans (by linarith)))

lemma innerBoundScaled : ∃ L>0, ∀ R > reachDistance x y, ∀ w : E4, w∈stage → w ≠ along →
     R^(10:ℕ) * ‖innerZone i t m n (outZ R) x y (R • w)‖ ≤ L / ‖w-along‖^3 := by
  obtain ⟨D,hD,he⟩ := price (mixed_rays i t)
  obtain ⟨M,hM,hμ⟩ := boundedSlope t m n
  refine ⟨D*M,by positivity,fun R hR w hw hw' => ?_⟩
  have hr := (horizon x y hR.le).1
  have hx := (small_reset x y hR.le).1
  have hy := (small_reset x y hR.le).2
  unfold innerZone; split_ifs
  · rw [outZ,norm_mul,← smul_sub]
    let I := integralInput t m n
    have H1 : R^4 * mixed i t (R • (along-w)) = mixed i t (along-w) := (mixed_rays i t).stretch (sub_ne_zero.mpr hw'.symm) hr.ne'
    have H2 (u : E4) (hu : u∈stage) : R^6 * I x y (R•u) = I (R⁻¹ • x) (R⁻¹ • y) u := by simpa only [I, smul_inv_smul₀ hr.ne'] using input_energy _ _ t m n hr.ne' u (apart hu hx) (apart hu hy)
    change R^10 * (‖mixed i t _‖ * ‖I _ _ _ - I _ _ _‖) ≤ _
    suffices e : ‖mixed i t (along-w)‖ * ‖I (R⁻¹•x) (R⁻¹•y) w-I (R⁻¹•x) (R⁻¹•y) along‖ ≤ D*M / ‖w-along‖^3 by
      rw [←H1,←H2 w hw,←H2 along stage_self,←mul_sub,norm_mul,norm_mul, Real.norm_of_nonneg (pow_nonneg hr.le 4),Real.norm_of_nonneg (pow_nonneg hr.le 6)] at e
      calc _ = _ := by rw [pow_add R 4 6];ring
           _ ≤ _ := e
    have h := norm_pos_iff.mpr (sub_ne_zero.mpr hw')
    have e := he _ (sub_ne_zero.mpr hw'.symm)
    rw [norm_sub_rev along w] at e
    apply mul_le_mul e (hμ _ hx _ hy w hw along stage_self) (norm_nonneg _) (by positivity) |>.trans
    field_simp; exact le_rfl
  rw [norm_zero,mul_zero]; positivity

def inflatedInner (R : ℝ) (w : E4) := R^8 * innerZone i t m n (outZ R) x y (R • w)
def spike (L : ℝ) (w : E4) := if w∈stage then L / ‖w-along‖^3 else 0
lemma spike_bound {L R:ℝ} (hL : 0<L) (bound : ∀ w ∈ stage, w ≠ along → R^(10:ℕ) * ‖innerZone i t m n (outZ R) x y (R • w)‖ ≤ L / ‖w-along‖^3)
   (hr : reachDistance x y ≤ R) (hR : 1 < R) (w) (he : w ≠ along) :
     ‖inflatedInner x y i t m n R w‖ ≤ spike L w := by
   by_cases h : w∈stage
   · rw [inflatedInner,norm_mul,Real.norm_of_nonneg (by positivity)]
     exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR.le (by decide : 8≤10)) (by positivity)).trans (by rw [spike,if_pos h]; exact bound w h he)
   simp only [spike,if_neg h,inflatedInner]
   unfold innerZone; rw [if_neg (fun t=>h (restaged x y hr t)),mul_zero,norm_zero]
lemma spike_pay (L : ℝ) (hL : 0<L) : Integrable (spike L) := by
  let f := fun w : E4=>if w∈closedBall 0 (5/8) then L / ‖w‖^3 else 0
  have he (w : E4) : ‖f w‖ ≤ L * ‖w‖ ^ (-(3:ℕ):ℝ) := by
    unfold f; split_ifs <;> (rw [Real.norm_of_nonneg (by positivity), inv_power]) <;> solve | rw [div_eq_mul_inv] | exact by positivity
  have hi := (locallyIntegrable_of_norm_le_rpow (f:=f) (C:=L) (α:=(3:ℕ)) (μ:=volume) (by norm_num [four_rank]) (by norm_num [four_rank]) (Eventually.of_forall he)
    ((Measurable.ite isClosed_closedBall.measurableSet (measurable_const.div (measurable_id.norm.pow_const _)) measurable_const).aestronglyMeasurable)).integrableOn_isCompact (isCompact_closedBall (0:E4) (5/8))
  suffices q : Integrable f volume by
     convert! q.comp_sub_right along using 1
     ext w; simp only [spike,stage,f,mem_closedBall_iff_norm,sub_zero]
  have eq (u) (hu:u∈(closedBall 0 (5/8:ℝ))ᶜ) : f u=0 := if_neg hu
  exact integrableOn_univ.mp (by simpa only [union_compl_self] using hi.union ((integrableOn_congr_fun_ae (g:=fun _:E4=>(0:ℝ)) (s:=(closedBall 0 (5/8))ᶜ) (ae_restrict_of_forall_mem isClosed_closedBall.measurableSet.compl eq)).mpr (by simp)))

lemma innerPoint (w) (hw : w≠along) : Tendsto (inflatedInner x y i t m n · w) atTop (𝓝 0) := by
  by_cases h : w∈stage
  · obtain ⟨L,hL,hE⟩ := innerBoundScaled x y i t m n
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have ht : Tendsto (fun R : ℝ=>R⁻¹ ^(2:ℕ) * (L/‖w-along‖^3)) atTop (𝓝 0) := (by simpa using tendsto_inv_atTop_zero.pow 2 |>.mul_const (L/‖w-along‖^3))
    apply squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) _ ht
    filter_upwards [eventually_gt_atTop (reachDistance x y)] with R hR
    have e := (horizon x y hR.le).1
    rw [inflatedInner,norm_mul,Real.norm_of_nonneg (by positivity),inv_pow]
    rw [le_inv_mul_iff₀' (by positivity)]
    rw [mul_right_comm (R^8),←pow_add]
    exact hE R hR w h hw
  exact (tendsto_congr' ((eventually_ge_atTop (reachDistance x y)).mono (fun R hr=> by
    simp [inflatedInner,innerZone, if_neg (fun hu=>h (restaged x y hr hu))]))).mpr tendsto_const_nhds
lemma inflatedInner_limit : Tendsto (fun R => R^4 * (∫ w,innerZone i t m n (outZ R) x y w)) atTop (𝓝 0) := by
  obtain ⟨L,hL,hE⟩ := innerBoundScaled x y i t m n
  have hm (R) : AEStronglyMeasurable (inflatedInner x y i t m n R) volume :=
     ((innerMeasurable i t m n (outZ _) x y).comp (f:=fun v:E4=>R • v) (measurable_id.const_smul R)).const_mul _ |>.aestronglyMeasurable
  have he := tendsto_integral_filter_of_dominated_convergence (μ:=volume) (F:=inflatedInner x y i t m n) _ (Eventually.of_forall hm)
    (((eventually_gt_atTop (reachDistance x y)).and (eventually_gt_atTop 1)).mono (fun R h => (volume.ae_ne along).mono (fun w hw=>spike_bound x y i t m n hL (hE R h.1) h.1.le h.2 w hw)))
    (spike_pay L hL) ((volume.ae_ne along).mono (innerPoint x y i t m n))
  rw [integral_zero] at he
  refine he.congr' ((eventually_gt_atTop (0:ℝ)).mono (fun R h=> ?_))
  rw [show (∫ a, inflatedInner x y i t m n R a)=_ from integral_const_mul ..,Measure.integral_comp_smul_of_nonneg volume _ _ (hR:=h.le),four_rank, smul_eq_mul]
  field_simp
lemma against_limit (hx : x≠y) : Tendsto (fun R => R^4 * against i t m n (outZ R) x y) atTop (𝓝 ( (if i=t then -4*normal else 0) * ∫ w, integralInput t m n x y w)) := by
  simpa only [against,mul_add,zero_add] using (inflatedInner_limit x y i t m n).add (inflateLimit x y i t m n hx)

end YM.Pert.Triangle
