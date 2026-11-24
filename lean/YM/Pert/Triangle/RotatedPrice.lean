import YM.Pert.Triangle.Ballistic
import YM.Pert.Triangle.Inflation

/-! Ball around moving vertex in arbitrary direction, rescaled edge and displaced singularity in difference coordinates. -/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
namespace YM.Pert.Triangle
open Maxwell Analysis Set Metric Function Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace Classical
local notation "I3" => Fin 3

def ringed := {w:E4 | 1/3 ≤ ‖w‖} ∩ closedBall 0 2
def shifted (d : E4) := closedBall d (5/8)
lemma ringedCompact : IsCompact ringed := (isCompact_closedBall _ _).inter_left ((isClosed_le continuous_const continuous_norm))
lemma in_ring {d:E4} (h : ‖d‖=1) : shifted d ⊆ ringed := by
  intro u hu
  have h':=mem_closedBall_iff_norm.mp hu
  have hi : 1/3 ≤ ‖u‖ := by have := norm_sub_norm_le d u; rw [norm_sub_rev] at this; linarith
  exact ⟨hi, mem_closedBall_iff_norm.mpr (by rw [sub_zero];linarith [norm_sub_norm_le u d])⟩
lemma peels {u v:E4} (hu : u∈ringed) (hv:v ∈small) : u≠v := by
  intro r
  simp only [ringed,small,mem_inter_iff,mem_setOf_eq,mem_closedBall_iff_norm,r,sub_zero] at hu hv
  linarith
variable (t m n i:I3)
def halo (L:ℝ) (w:E4) := if w∈closedBall 0 (5/8) then L / ‖w‖^3 else 0
lemma halo_pay (L : ℝ) (hL : 0<L) : Integrable (halo L) := by
   have h : (halo L) = (fun w=>spike L (w+along)) := funext (fun w=>by unfold halo spike stage;rw [mem_closedBall_iff_norm,mem_closedBall_iff_norm,sub_zero,add_sub_cancel_right])
   change Integrable (halo L) volume; rw [h]; exact (spike_pay L hL).comp_add_right _
lemma universalSlope :
    ∃ M>0, ∀ x∈small,∀ y∈small,∀ d:E4, ‖d‖=1 → ∀ v∈shifted d,
       ‖integralInput t m n x y v - integralInput t m n x y d‖ ≤ M * ‖v-d‖ := by
  let f := fun z : E4 × E4 × E4 => integralInput t m n z.1 z.2.1 z.2.2
  let A := small ×ˢ small ×ˢ ringed
  have hA : IsCompact A := small_compact.prod (small_compact.prod ringedCompact)
  have hcont (z) (hz : z∈A) : ContDiffAt ℝ 1 f z := by
     have hi : z.2.2-z.1 ≠ 0 := sub_ne_zero.mpr (peels hz.2.2 hz.1)
     have hj : z.2.2-z.2.1 ≠ 0 := sub_ne_zero.mpr (peels hz.2.2 hz.2.1)
     unfold f integralInput
     refine ContDiffAt.sum (fun a _=> ContDiffAt.sum fun b _=> ?_)
     refine (contDiffAt_const.mul ?_).mul ?_
     · apply ContDiffAt.comp (g:=mLine m a) (f:=fun z : E4 × E4 × E4 => z.2.2-z.1) _ ((mLine_regular m a hi).of_le (by decide))
       apply ContDiffAt.sub <;> fun_prop
     apply ContDiffAt.comp (g:=mLine n b) (f:=fun z : E4 × E4 × E4 => z.2.2-z.2.1) _ ((mLine_regular n b hj).of_le (by decide))
     apply ContDiffAt.sub <;> fun_prop
  obtain ⟨D,hD⟩ := hA.exists_bound_of_continuousOn (f:=fderiv ℝ f) (fun v hv=> (hcont v hv |>.continuousAt_fderiv (by decide)).continuousWithinAt)
  refine ⟨|D|+1,by positivity,fun x hx y hy d hd v hv=>?_⟩
  have subs : (small ×ˢ small ×ˢ shifted d) ⊆ A := fun _ h=> ⟨h.1,h.2.1,in_ring hd h.2.2⟩
  have hcx : Convex ℝ (small ×ˢ small ×ˢ shifted d) := Convex.prod (convex_closedBall ..) (Convex.prod (convex_closedBall ..) (convex_closedBall ..))
  have he := hcx.norm_image_sub_le_of_norm_fderiv_le (x:=(x,y,d)) (y:=(x,y,v)) (𝕜:=ℝ) (fun z hz=>(hcont z (subs hz)).differentiableAt (by decide)) (fun z hz=>hD z (subs hz)) ⟨hx,hy,mem_closedBall_self (by norm_num)⟩ ⟨hx,hy,hv⟩
  simpa [f,-ge_iff_le] using (show _ ≤ (|D|+1) * ‖(x,y,v) - (x,y,d)‖ from he.trans (by gcongr; exact (le_abs_self _).trans (by linarith)))
-- general bound
lemma sphericalPrice : ∃ C>0, ∀ x y d B r, ‖d‖=1 → 8<B → ‖x‖ ≤ B → ‖y‖≤B → 8*B < r → ∀w:E4,w≠0 →
     r^(10:ℕ) * ‖innerZone i t m n (radial r d) x y (r • (w+d))‖ ≤ halo C w := by
  obtain ⟨D,hD,he⟩ := price (mixed_rays i t)
  obtain ⟨M,hM,hμ⟩ := universalSlope t m n
  refine ⟨D*M,by positivity,fun x y d B R hd hB bx by' hR w hw' => ?_⟩
  have hr : 0<R := by linarith
  have hsmall (v:E4) (hv:‖v‖≤B): R⁻¹ •v ∈ small := by
      rw [small,mem_closedBall_iff_norm,sub_zero,norm_smul, Real.norm_of_nonneg (by positivity),inv_mul_le_iff₀ hr]
      linarith
  have hx := hsmall _ bx
  have hy := hsmall _ by'
  unfold innerZone; split_ifs with hhit
  · rw [radial,norm_mul,← smul_sub] 
    have hw0 : w∈closedBall (0:E4) (5/8) := by
      have h := mem_closedBall_iff_norm.mp hhit
      rw [radial,← smul_sub,add_sub_cancel_right,norm_smul,Real.norm_of_nonneg hr.le] at h
      exact mem_closedBall_iff_norm.mpr (by rw [sub_zero]; exact (mul_le_mul_iff_right₀ hr).mp (h.trans (rangeHole hd hR bx by').2))
    have wd : along-along+w+d = w+d := by rw [sub_self,zero_add]
    have hw : (w+d)∈shifted d := mem_closedBall_iff_norm.mpr (by simpa only [add_sub_cancel_right,sub_zero] using (mem_closedBall_iff_norm.mp hw0))
    have hdr : d∈shifted d := mem_closedBall_self (by norm_num)
    let I := integralInput t m n
    let x' := R⁻¹ • x
    let y' := R⁻¹ • y
    have H1 : R^4 * mixed i t (R • (d-(w+d))) = mixed i t (d-(w+d)) := (mixed_rays i t).stretch (by rw [sub_add_cancel_right]; exact neg_ne_zero.mpr hw') hr.ne' -- wrong
    have H2 (u : E4) (hu : u∈shifted d) : R^6 * I x y (R•u) = I x' y' u := by
      have hsu:=in_ring hd hu
      simpa only [I,x',y', smul_inv_smul₀ hr.ne'] using input_energy x' y' t m n hr.ne' u (peels hsu hx) (peels hsu hy)
    change R^10 * (‖mixed i t _‖ * ‖I _ _ _ - I _ _ _‖) ≤ _
    rw [halo,if_pos hw0]
    suffices e : ‖mixed i t (d-(w+d))‖ * ‖I x' y' (w+d)-I x' y' d‖ ≤ D*M / ‖w‖^3 by
      rw [←H1,←H2 _ hw,←H2 d hdr,←mul_sub,norm_mul,norm_mul, Real.norm_of_nonneg (pow_nonneg hr.le 4),Real.norm_of_nonneg (pow_nonneg hr.le 6)] at e
      calc _ = _ := by rw [pow_add R 4 6];ring
           _ ≤ _ := e
    have h := norm_pos_iff.mpr hw'
    have e := he _ (neg_ne_zero.mpr hw')
    rw [norm_neg w] at e
    have hEq : d-(w+d) = -w := by abel
    rw [hEq]
    have q := hμ _ hx _ hy d hd _ hw
    dsimp only [I,x',y'];rw [add_sub_cancel_right] at q
    apply mul_le_mul e q (norm_nonneg _) (by positivity) |>.trans
    field_simp; exact le_rfl
  rw [norm_zero,mul_zero]; unfold halo; split_ifs <;> positivity

open Filter Asymptotics
section
variable {X Y δ:ℕ→E4} {d:E4} {R:ℕ→ℝ} {B:ℝ} (hR:Tendsto R atTop atTop) (hB:8<B) (bx:∀ k,‖X k‖≤B) (by':∀ k, ‖Y k‖≤B) (hU:∀ k,‖δ k‖=1)
include hR hB bx by' hU
lemma coreLimit : Tendsto (fun k=> (R k)^4 * (∫ w,innerZone i t m n (radial (R k) (δ k)) (X k) (Y k) w)) atTop (𝓝 0) := by
  obtain ⟨L,hL,hE⟩ := sphericalPrice t m n i
  let F (k :ℕ) := innerZone i t m n (radial (R k) (δ k)) (X k) (Y k)
  let g k w := (R k)^8 * F k (R k • (w+δ k))
  have hm (k) : AEStronglyMeasurable (g k) volume :=
     ((innerMeasurable i t m n _ _ _).comp (f:=fun v:E4=>R k • (v+δ k)) ((show Continuous (fun v:E4=>R k • (v+δ k)) from by fun_prop).measurable)).const_mul _ |>.aestronglyMeasurable
  have ev : ∀ᶠ k in atTop, 8*B < R k ∧ 1<R k := hR.eventually ((eventually_gt_atTop _).and (eventually_gt_atTop _))
  have eq : ∀ᶠ k in atTop, ∀ w ≠ 0, ‖g k w‖ ≤ ((R k)⁻¹^2)* halo L w := by
    filter_upwards [ev] with k hk w hw
    dsimp only [g,F]
    rw [norm_mul,Real.norm_of_nonneg (by positivity),inv_pow]
    rw [le_inv_mul_iff₀' (pow_pos (lt_trans zero_lt_one hk.2) 2)]
    rw [mul_right_comm (R k^8),←pow_add]
    exact hE _ _ _ B _ (hU k) hB (bx k) (by' k) hk.1 w hw
  have hh (w) : 0≤halo L w := by unfold halo;split_ifs <;> positivity
  have hb (k:ℕ) (h:1<R k) (w) : ((R k)⁻¹^2)*halo L w ≤ halo L w := mul_le_of_le_one_left (hh w) (by
        exact (sq_le_one_iff_abs_le_one _).mpr (by rw [abs_of_pos (by positivity)]; simpa only [one_div,inv_one] using one_div_le_one_div_of_le zero_lt_one h.le))
  have he := tendsto_integral_filter_of_dominated_convergence (μ:=volume) (F:=g) (f:=fun _:E4=>0) _ (Eventually.of_forall hm)
    ((ev.and eq).mono (fun k h => (volume.ae_ne (0:E4)).mono (fun w hw=> (h.2 w hw).trans (hb k h.1.2 w))))
    (halo_pay L hL) ((volume.ae_ne 0).mono fun w hw=> (tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) (eq.mono (fun _ h=>h w hw)) (by simpa using (((tendsto_inv_atTop_zero.comp hR).pow 2).mul_const (halo L w))))))
  rw [integral_zero] at he
  refine he.congr' ((hR.eventually (eventually_gt_atTop (0:ℝ))).mono (fun k h=> ?_))
  unfold g
  rw [integral_const_mul]
  suffices (∫ w,F k (R k • (w+δ k))) = ∫ w,F k (R k • w) by
    rw [this,Measure.integral_comp_smul_of_nonneg volume _ _ (hR:=h.le),four_rank, smul_eq_mul]
    unfold F
    field_simp
  convert! MeasureTheory.integral_add_right_eq_self (fun w=> F k (R k • w)) (δ k) (μ:=volume)
end
end YM.Pert.Triangle
