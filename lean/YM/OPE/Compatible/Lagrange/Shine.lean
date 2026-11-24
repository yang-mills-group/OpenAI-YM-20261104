import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Complex.CauchyIntegral
/-!
# Reading from a thick grid: circle remainder separate from real interpolation cost
-/
set_option autoImplicit false
noncomputable section
namespace YM.FrameRead
open Function Filter Metric Polynomial Finset Complex
open scoped BigOperators Topology
variable {ι : Type*}[DecidableEq ι]{s:Finset ι}{v:ι→ℂ}{A R:ℝ}{f:ℂ→ℂ}
private lemma divs (hs:s.Nonempty)(hv:Set.InjOn v s) (he:∀ i∈s, v i ≠ 0) (z:ℂ)(hz:z≠0)(hh:∀ i∈s,z≠v i):
    (z-0)⁻¹ - (∑ i ∈ s,eval 0 (Lagrange.basis s v i)*(z-v i)⁻¹) = z⁻¹ * (eval 0 (Lagrange.nodal s v)/eval z (Lagrange.nodal s v)):=by
    let P:= Lagrange.nodal s v; let w:= Lagrange.basis s v
    have hw(x:ℂ): ∑ i∈s,eval x (w i)=1:=by rw [← eval_finsetSum,Lagrange.sum_basis (v:=v) hv hs,eval_one] -- w reduction
    have h0:eval z P≠0:= Lagrange.eval_nodal_not_at_node hh
    have ha i (hi:i∈s): eval 0 (w i) * (z-v i)⁻¹ = z⁻¹ * (eval 0 (w i)- (eval 0 P/eval z P)*eval z (w i)):=by
       unfold w; rw [Lagrange.eval_basis_not_at_node hi (Ne.symm (he i hi)),Lagrange.eval_basis_not_at_node hi (hh i hi)]; change eval 0 P * _ * _ = z⁻¹* (eval 0 P* _ - _*(eval z P*_)); have ht:= he i hi; have he:=sub_ne_zero.mpr (hh i hi); field_simp; ring
    change _ - (∑ i∈ s,eval 0 (w i)*_) = _
    rw [sum_congr rfl ha,← mul_sum,sum_sub_distrib,← mul_sum,hw,hw]; unfold P; ring
lemma contour_value (hs:s.Nonempty)(hv:Set.InjOn v s)(he:∀ i∈s,v i ≠0) (hr:0<R)(hp:∀ i∈s,‖v i‖ ≤ R/3)(hh:DifferentiableOn ℂ f (closedBall 0 R))(hf:∀ z:ℂ,‖z‖=R→ ‖f z‖ ≤ A):
    ‖f 0-(∑ i∈s,eval 0 (Lagrange.basis s v i)*f (v i))‖ ≤ A*(1/2:ℝ)^s.card:=by
    have hw(i)(hx:i∈s):v i∈ ball (0:ℂ) R:=mem_ball_zero_iff.mpr ((hp i hx).trans_lt (by linarith)); let P:= Lagrange.nodal s v; let k(x z:ℂ):=(z-x)⁻¹*f z; let t:ℂ:=2*Real.pi*Complex.I; let w i:=eval 0 (Lagrange.basis s v i)
    have hl(x:ℂ)(hx:x∈ball (0:ℂ) R): CircleIntegrable (k x) 0 R:=by
       apply ContinuousOn.circleIntegrable hr.le; refine ContinuousOn.mul (f:=fun y:ℂ=> (y-x)⁻¹) (((continuousOn_id.sub continuousOn_const).inv₀ (fun i hi=>sub_ne_zero.mpr ?_))) (hh.continuousOn.mono sphere_subset_closedBall)
       rintro rfl; exact Metric.sphere_disjoint_ball.le_bot ⟨hi,hx⟩ -- mem
    have ht(x:ℂ)(hx:x∈ ball (0:ℂ) R): t⁻¹*(∮ z in C(0,R), k x z)= f x:=(hh.mono closure_ball_subset_closedBall).diffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hx
    let r(z:ℂ):= z⁻¹ * (eval 0 P/eval z P)*f z
    let u(z):= k 0 z- ∑ i∈s,w i*k (v i) z
    have hh'(z:ℂ)(hz:z∈sphere (0:ℂ) R)(i)(hi:i∈s):z≠v i:=fun h=> (not_lt.mpr (le_of_eq hz.symm) (Metric.mem_ball.1 (h ▸ hw i hi))) -- rewrite orientation
    have hc : (∮ z in C(0,R),u z)=∮ z in C(0,R),r z:=circleIntegral.integral_congr hr.le fun z hz=>by
       have hu:‖z‖=R:= by simpa using hz
       have hf':z≠0:=norm_ne_zero_iff.mp (hu.symm ▸ hr.ne')
       unfold u k w; simp_rw [← mul_assoc,← sum_mul]; rw [← sub_mul, divs hs hv he z hf' (hh' z hz)]
    have hφ: f 0 - (∑ i∈s,w i*f (v i))= t⁻¹*(∮ z in C(0,R),r z):=by
       rw [← hc]; unfold u; have hF z (hz:z∈s):CircleIntegrable (fun j=>w z * k (v z) j) 0 R:= (hl _ (hw z hz)).const_mul (w z) -- name
       have hh: CircleIntegrable (fun z=> ∑ i∈ s,w i*k (v i) z) 0 R :=by
          have hx:=CircleIntegrable.sum s hF; rw [show (fun z=> ∑ i∈s, w i*k (v i) z) = ∑ i∈s,(fun z=>w i*k (v i) z) from funext fun _=> by simp [Finset.sum_apply]]; exact hx
       rw [circleIntegral.integral_sub (hl _ (mem_ball_self hr)) hh, circleIntegral.integral_fun_sum hF,mul_sub, ht _ (mem_ball_self hr),mul_sum]
       congr 1; refine sum_congr rfl fun i hi=>?_ ; rw [circleIntegral.integral_const_mul,mul_left_comm, ht _ (hw i hi)]
    have hb := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (f:=r) (C:=(R⁻¹ * (1/2:ℝ)^s.card)*A) hr.le (c:=0)
    change ‖f 0 - (∑ i∈s,w i*f (v i))‖ ≤ _; rw [hφ]; refine (hb ?_).trans_eq ?_; swap; field_simp
    intro z hz; have hu: ‖z‖= R:= by simpa using hz
    unfold r; rw [norm_mul,norm_mul,norm_inv,hu]; refine ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hr.le)) (norm_nonneg (f z))).trans (mul_le_mul_of_nonneg_left (hf z hu) (by positivity)))
    unfold P; rw [Lagrange.eval_nodal,Lagrange.eval_nodal,← prod_div_distrib, norm_prod, ← Finset.prod_const]; refine prod_le_prod (fun _ _=> norm_nonneg _) fun i hi=> ?_
    rw [norm_div,zero_sub,norm_neg]; refine (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr (hh' z hz i hi)))).mpr ?_; linarith only [hp i hi,norm_sub_norm_le z (v i), hu]
end YM.FrameRead
