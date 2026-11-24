import YM.MSbar.Dim.HighDim
import Mathlib.Analysis.Complex.Schwarz

/-! A second transfer principle to be used beyond the fixed-polynomial moment identity:
class of dimensionally continued kernel operations which are determined by their integer values
on each ambient space. Use after normalizing Mellin costs for each loop. Based on Blaschke growth
at a whole half-plane. Never assume any analyticity in loop order, lattice spacing, nor in g.
It is NOT assuming integer-value extension of arbitrary analytic identities in ε. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Transfer
open Complex Metric Filter Set MeasureTheory Function
open scoped Topology ContDiff BigOperators Classical

def half := {z:ℂ|0<z.re}
theorem open_h : IsOpen half:= isOpen_lt continuous_const continuous_re
variable {f : ℂ→ℂ} {t M : ℝ} {z : ℂ} (ht : 0<t)
include ht
lemma ball_key (hz : z∈half) : z+ (↑t:ℂ) ≠ 0:=by
    intro h; replace h:=congr_arg Complex.re h; simp at h; change 0 < z.re at hz; linarith
lemma disk (hz : z∈half) : (z-(↑t:ℂ))/(z+(↑t:ℂ))∈ ball (0:ℂ) 1:=by
    rw [mem_ball_zero_iff,norm_div,div_lt_one (norm_pos_iff.mpr (ball_key ht hz))]
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    simp [Complex.sq_norm, Complex.normSq_apply]; change 0 < z.re at hz; nlinarith
omit ht in
lemma disk_key (hz : z∈ ball (0:ℂ) 1): 1-z ≠ 0:=by intro h; rw [← sub_eq_zero.mp h,mem_ball_zero_iff,norm_one] at hz; exact lt_irrefl _ hz
lemma lift (hz : z∈ ball (0:ℂ) 1) : (↑t:ℂ)*((1+z)/(1-z))∈half:=by
    change 0 < Complex.re _; rw [mul_re, ofReal_re,ofReal_im,zero_mul,sub_zero]; apply mul_pos ht
    have he:= mem_ball_zero_iff.mp hz; have hx:= normSq_pos.mpr (disk_key hz); have ht := Complex.sq_norm z
    rw [div_re,← add_div]; apply div_pos _ hx; simp only [add_re,sub_re,add_im,sub_im,one_re,one_im]; simp only [normSq_apply] at ht; nlinarith [norm_nonneg z]
lemma again (hz : z∈half) : (↑t:ℂ)*((1+(z-t)/(z+t))/(1-(z-t)/(z+t)))=z:=by
   have hT:= ball_key ht hz; have hY:= disk_key (disk ht hz); have hP : (t:ℂ)≠0:= by exact_mod_cast ht.ne'
   field_simp; ring_nf; rw [mul_right_comm, mul_inv_cancel₀ hP,one_mul]

lemma price (hf : DifferentiableOn ℂ f half) (hg : f (t:ℂ)=0) (hM : ∀ z∈half, ‖f z‖ ≤ M) : ∃ g:ℂ→ℂ,
    DifferentiableOn ℂ g half ∧ (∀ z∈half,‖g z‖ ≤ M) ∧ ∀ z∈half,f z=(z-t)/(z+t)*g z:=by
    let a:ℂ:=↑t; let g(z:ℂ):=(z+a)*dslope f a z
    have he:a∈half:=ht
    have h1 : DifferentiableOn ℂ g half:= (differentiableOn_id.add_const _).mul ((differentiableOn_dslope (open_h.mem_nhds he)).mpr hf)
    have heq(z:ℂ)(hz:z∈half): f z=(z-a)/(z+a)*g z := by
       unfold g; have hB := ball_key ht hz; rw [div_mul_eq_mul_div,← mul_assoc ((z-a)), mul_comm (z-a) (z+a),mul_assoc,mul_div_cancel_left₀ _ hB]; exact Eq.symm (sub_smul_dslope_of_zero hg z)
    let k(z:ℂ):=a*((1+z)/(1-z))
    have hd : DifferentiableOn ℂ (f ∘ k) (ball (0:ℂ) 1):= hf.comp (fun z hz=> by
       change DifferentiableWithinAt ℂ (fun z=> a*((1+z)/(1-z))) _ _; fun_prop (disch:=exact disk_key hz)) (mapsTo_iff_image_subset.mpr fun z hz=> by obtain ⟨y,h,rfl⟩:=hz; exact lift ht h)
    have hw:(f∘k) 0=0:=by simp [k,comp,a,hg] -- typo
    have hp (z:ℂ)(hz:z∈half) (h:z≠a): ‖g z‖ ≤ M:=by
       let c:=(z-a)/(z+a); have hh:= dist_le_div_mul_dist_of_mapsTo_ball hd (show MapsTo (f ∘ k) _ (closedBall _ M) from ?_) (disk ht hz)
       · rw [hw,comp_apply, show k c=z from again ht hz] at hh; simp only [dist_zero_right,div_one,heq z hz,norm_mul] at hh
         rw [mul_comm M] at hh; exact le_of_mul_le_mul_left hh (norm_pos_iff.mpr (div_ne_zero (sub_ne_zero.mpr h) (ball_key ht hz))) -- cycle simp heq?
       rw [hw]; exact fun z hz=> mem_closedBall_zero_iff.mpr (hM _ (lift ht hz))
    refine ⟨g,h1,fun z hz=>?_,heq⟩; rcases eq_or_ne z a with hw|hw
    · subst z; refine le_of_tendsto (show Tendsto (fun x:ℂ=>‖g x‖) (𝓝[≠] a) (𝓝 ‖g a‖) from (h1.continuousOn.continuousAt (open_h.mem_nhds he)).norm.continuousWithinAt) ?_
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (open_h.mem_nhds he)] with v hx hh; exact hp v hh hx
    exact hp z hz hw
end YM.MSbar.Transfer
