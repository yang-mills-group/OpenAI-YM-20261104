import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RealDeriv
import YM.OPE.Log.Wallet

/-!
# Polynomial mesh resolution via damped holomorphic extensions

Instead of Lagrange interpolation with very high variable order: if analytic on
unit disc, pay polynomial N on a smaller mesh using the sup of the entire REAL
segment, even when crude complex bounds are exp N. Combined with interior
penalized maximum, this lets us import a grid estimate on *values* alone.

Strict proof: upper semi-disc maximum principle, with explicit damping. Then also
lower, for sensitivity estimate by Cauchy.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Polar
open Function Set Filter Metric Complex Real
open scoped Topology BigOperators
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X]
variable {F:ℂ→X} {N A:ℝ}
set_option quotPrecheck false
section
local notation "D"=> closedBall (0:ℂ) 1
local notation "B"=> ball (0:ℂ) 1
local notation "C"=> D∩{x:ℂ|0≤x.im}

variable (hN:1 ≤ N)(hd: ∀ z∈ closedBall (0:ℂ) 1,DifferentiableAt ℂ F z)
    (h:∀ z:ℂ, ‖z‖≤1→ ‖F z‖ ≤ Real.exp N) (hx:∀ x:ℝ, |x|≤1→ ‖F (x:ℂ)‖ ≤ A) (ha:1 ≤ A)
private def weigh (N:ℝ)(z:ℂ):= Complex.exp ((N:ℂ)*(3*I*z-z^2))
private lemma level (N:ℝ)(z:ℂ) : ‖weigh N z‖ = Real.exp (N*(-3*z.im+z.im^2-z.re^2)):= by simp [weigh,norm_exp,pow_two,Complex.mul_re,Complex.mul_im]; congr 1; ring_nf; simp

include hN h hd hx ha
lemma pricing {z:ℂ}(hz: ‖z‖ ≤ N⁻¹)(hp:0 ≤ z.im) : ‖F z‖ ≤ Real.exp 4*A :=by
    have hN':0<N :=zero_lt_one.trans_le hN; let f (z:ℂ):= weigh N z • F z; let U:=C
    have hC:IsClosed (U) := (isClosed_closedBall).inter (isClosed_le continuous_const continuous_im) -- case
    have hf:DifferentiableOn ℂ f U:=fun x hx=> ((show DifferentiableAt ℂ (weigh N) x from by unfold weigh; fun_prop).smul (hd x hx.1)|>.differentiableWithinAt)
    have hD:DiffContOnCl ℂ f U:= ⟨hf,hC.closure_eq.symm ▸ hf.continuousOn⟩ -- cast
    have he : ∀ x∈ frontier U, ‖f x‖ ≤ A:= by
       intro x hx'; have hy:= hC.closure_eq ▸ (frontier_subset_closure hx') -- problematic dep
       have hw:0 ≤ x.im:= hy.2; have h'A : ‖x‖ ≤ 1:= by simpa using (mem_closedBall.mp hy.1)
       unfold f; rw [norm_smul,level]
       by_cases hz:x.im=0
       · apply le_trans (mul_le_of_le_one_left (norm_nonneg _) ((Real.exp_le_one_iff).2 (mul_nonpos_of_nonneg_of_nonpos hN'.le (by rw [hz]; nlinarith only [sq_nonneg x.re])))); rw [show x= (x.re:ℂ) from (Complex.ext rfl (by simpa using hz))] -- will rewrite RHS x too only goal
         exact hx x.re ((Complex.abs_re_le_norm x).trans h'A)
       have ht: ‖x‖=1:=by
          refine eq_of_le_of_not_lt h'A fun ht=> hx'.2 ?_; exact mem_interior_iff_mem_nhds.mpr (inter_mem (mem_of_superset (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr ht)) ball_subset_closedBall) (mem_of_superset ((isOpen_lt continuous_const continuous_im).mem_nhds (show 0 < x.im from lt_of_le_of_ne hw (Ne.symm hz))) (fun (j:ℂ) (h:0<j.im)=> h.le))) -- lemmas names
       have hE : N * (-3*x.im+x.im^2-x.re^2) ≤ -N:= by
          rw [show -N=N*(-1) from by ring]; apply mul_le_mul_of_nonneg_left _ hN'.le; have he: x.im ≤ 1:= (le_abs_self _).trans ((abs_im_le_norm _).trans h'A); nlinarith only [sq_norm_sub_sq_re x, (mul_le_mul_of_nonneg_left he hw),sq_nonneg x.re, (by rw [ht]; norm_num : ‖x‖^2=1), he,hw] -- multiply?
       apply le_trans (mul_le_mul (Real.exp_monotone hE) (h x h'A) (norm_nonneg _) (Real.exp_nonneg _)); rwa [← Real.exp_add, neg_add_cancel,Real.exp_zero]
    have ht : N⁻¹ ≤ 1:= inv_le_one_of_one_le₀ hN; have h' := Complex.norm_le_of_forall_mem_frontier_norm_le (U:=U) (isBounded_closedBall.subset inter_subset_left) hD he (subset_closure (show z∈U from ⟨mem_closedBall_zero_iff.mpr (hz.trans ht),hp⟩))
    have hu: -4 ≤ N*(-3*z.im+z.im^2-z.re^2):= by
       have hs : z.im ≤ N⁻¹:= (le_abs_self _).trans ((abs_im_le_norm _).trans hz)
       have hv: z.re^2 ≤ N⁻¹:=by nlinarith only [sq_nonneg z.im,sq_norm_sub_sq_re z, (mul_le_of_le_one_right (norm_nonneg z) (hz.trans ht)),hz]
       have he:= mul_le_mul_of_nonneg_left hs hN'.le; have hx:= mul_le_mul_of_nonneg_left hv hN'.le; rw [mul_inv_cancel₀ hN'.ne'] at he hx; nlinarith only [he,hx,mul_nonneg hN'.le (sq_nonneg z.im)]
    unfold f at h'; rw [norm_smul, level] at h'; have hf:= (mul_le_mul_of_nonneg_right (Real.exp_monotone hu) (norm_nonneg _)).trans h'
    rw [Real.exp_neg] at hf; exact (le_div_iff₀ (by positivity : (0:ℝ)< (Real.exp 4)⁻¹)).mpr (le_trans ((mul_comm ..).le) hf)|>.trans_eq (by simp [div_eq_mul_inv,mul_comm])

lemma paid {z:ℂ}(hz: ‖z‖ ≤ N⁻¹) : ‖F z‖ ≤ Real.exp 4*A:=by
    rcases le_total 0 z.im with e|e; exact pricing hN hd h hx ha hz e
    have he:= pricing (F:=fun z=> F (-z)) (z:=-z) hN (fun x hx=>(hd (-x) (by simpa using hx)).comp (f:=fun z:ℂ=>-z) x (by fun_prop)) (fun x hx=> h _ (by simpa using hx)) (fun x h=>by simpa using hx (-x) (by simpa using h)) ha (by simpa using hz) (by simpa using e); simpa using he
lemma budget : ‖deriv F 0‖ ≤ Real.exp 4*A*N:=by
    have hP : 0<N:=zero_lt_one.trans_le hN
    have he: DiffContOnCl ℂ F (ball 0 N⁻¹):=by
       have hc:= closedBall_subset_closedBall (x:=(0:ℂ)) (inv_le_one_of_one_le₀ hN)
       have hh:DifferentiableOn ℂ F (closedBall 0 1):= fun x h=> (hd x h).differentiableWithinAt
       exact ⟨hh.mono (ball_subset_closedBall.trans hc), hh.continuousOn.mono (closure_minimal (ball_subset_closedBall.trans hc) isClosed_closedBall)⟩
    simpa only [div_eq_mul_inv,inv_inv] using Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (inv_pos.mpr hP) he (fun z hz=> paid hN hd h hx ha (by exact (mem_sphere_zero_iff_norm.mp hz).le))
end
end YM.OPE.Polar
