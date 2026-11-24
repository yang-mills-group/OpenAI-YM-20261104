import YM.Extra.FREE_DETECTOR_ALGEBRA.Average
import YM.Extra.FREE_DETECTOR_ALGEBRA.Radials
import YM.OPE.Compatible.Ash.Tea
/-!
# Compact log annuli
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Sagebrush
open Function MeasureTheory Set Topology Metric Filter Lattice Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
abbrev PureA:= SphereTest.Pure (F:=ℝ)
local notation "A" => E4→ℝ -- remove
variable {x:E4}{j k:ℕ}{g f:E4→ℝ}
lemma grad_won (he:g=ᶠ[𝓝 x] f) (a:Axis): grad a g=ᶠ[𝓝 x] grad a f:= (he.fderiv (𝕜:=ℝ)).mono fun _ hx=>congrArg (fun L:E4→L[ℝ]ℝ=>L (basis a)) hx
lemma Gp (g f:E4→ℝ)(hg:ContDiffAt ℝ ∞ g x)(hf:ContDiffAt ℝ ∞ f x)(a:Axis): grad a (g*f) x= grad a g x*f x+ g x*grad a f x:= grad_times hg hf a
-- only away smooth
lemma Lp (g f:E4→ℝ)(hg:∀ x∈away,ContDiffAt ℝ ∞ g x)(hf:∀ x∈away,ContDiffAt ℝ ∞ f x)(hx:x∈away): lap (g*f) x=lap g x*f x+g x*lap f x+2*∑ i:Axis, grad i g x * grad i f x:=by
    have he(i): grad i (g*f)=ᶠ[𝓝 x] (grad i g*f+g*grad i f):= by filter_upwards [open_away.mem_nhds hx] with y hy; exact Gp g f (hg y hy) (hf y hy) i
    have hh(i:Axis):grad i (grad i (g*f)) x= (grad i (grad i g) x*f x + g x*grad i (grad i f) x + 2*(grad i g x*grad i f x)):=by
       have H:= hg x hx; have L:= hf x hx; let H':=grad_smooth_at H i; let L':=grad_smooth_at L i; rw [(grad_won (he i) i).self_of_nhds, grad_plus (g:=g*grad i f) (show ContDiffAt ℝ ∞ (grad i g*f) x from H'.mul L) (H.mul L'), Gp _ _ H' L i,Gp _ _ H L' i]; ring
    simp_rw [lap,hh, Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
lemma lap_power (hx:x∈away) : lap (rr^(k+1)) x = (4*((k:ℝ)+1)*k)*rr x^(k+2):=by
    let m:=k+1; let v:ℝ:=-(2*m); let u:ℝ:= -(2*((m+1:ℕ):ℝ))
    have he(i:Axis):grad i (rr^m)=ᶠ[𝓝 x] (v • (rr^(m+1)*coordF i)):=by filter_upwards [open_away.mem_nhds hx] with y hy; change grad i (rr^m) y=v*(rr y^(m+1)*y i); rw [grad_power hy]; unfold v; push_cast; ring
    have H(i:Axis):grad i (grad i (rr^m)) x= (v*u*rr x^(m+2)*(x i)^2) + v*rr x^(m+1):=by
       have H:ContDiffAt ℝ ∞ (rr^(m+1)) x := (rr_smooth hx).pow _; rw [(grad_won (he i) i).self_of_nhds, grad_smul (show ContDiffAt ℝ ∞ (rr^(m+1)*coordF i) x from H.mul (pure_coordF i).smooth.contDiffAt), Gp _ _ H (pure_coordF i).smooth.contDiffAt,grad_coordF,if_pos rfl,grad_power hx]; change (v* ((u*rr x^(m+2)*x i)*x i+rr x ^(m+1)*1):ℝ)=_;ring
    have hh:= Pert.Full.norm_four x; change ∑ i:Axis, grad i (grad i (rr^m)) x=_
    simp_rw [H,Finset.sum_add_distrib,← Finset.mul_sum, ← hh]; simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; have hX:0 < ‖x‖:= norm_pos_iff.mpr hx; dsimp only [m,u,v]; push_cast; unfold rr; rw [pow_succ (_ : ℝ) (k+1+1)]; field_simp;ring
lemma coal_fin (hf:HasCompactSupport f)(hg:Continuous g)(hh:Continuous f):Integrable (fun x=>f x*g x):= (hh.mul hg).integrable_of_hasCompactSupport (HasCompactSupport.mul_right hf)
lemma grad_fin (hf:HasCompactSupport f)(a:Axis): HasCompactSupport (grad a f):= hf.fderiv_apply ℝ _
lemma grad_self_pay (hf:HasCompactSupport f)(hg:ContDiff ℝ ∞ g)(hh:ContDiff ℝ ∞ f)(a:Axis): (∫ x, f x *grad a g x) = -∫ x,grad a f x*g x:=by
   have ht := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (𝕜:=ℝ) (f:=f) (g:=g) (μ:=volume) (v:=basis a) (coal_fin (grad_fin hf a) hg.continuous (grad_diff_all hh a).continuous) (coal_fin hf (grad_diff_all hg a).continuous hh.continuous) (coal_fin hf hg.continuous hh.continuous) (fun x _=>hh.differentiable (by simp) x) (fun x _=>hg.differentiable (by simp) x); exact ht
lemma lap_self_pay (hf:HasCompactSupport f)(hg:ContDiff ℝ ∞ g)(hh:ContDiff ℝ ∞ f): (∫ x, f x *lap g x)= ∫ x, lap f x *g x:=by
    have he i: (∫ x,f x*grad i (grad i g) x)= ∫ x,grad i (grad i f) x*g x:=by rw [grad_self_pay hf (grad_diff_all hg i) hh i,grad_self_pay (grad_fin hf i) hg (grad_diff_all hh i) i]; simp
    simp_rw [lap,Finset.mul_sum, Finset.sum_mul, integral_finsetSum _ (fun i _=> coal_fin hf (grad_diff_all (grad_diff_all hg i) i).continuous hh.continuous), integral_finsetSum _ (fun i _=>coal_fin (grad_fin (grad_fin hf i) i) hg.continuous (grad_diff_all (grad_diff_all hh i) i).continuous), he]
end YM.OPE.Sagebrush
