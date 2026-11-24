import YM.OPE.Compatible.Mire.Beer
/-!
# Compact log annuli interop. Transition error exactly cancels by measure scaling
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Sagebrush
open Function MeasureTheory Set Topology Metric Filter Lattice Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
variable {x:E4}{k:ℕ}{f g:E4→ℝ}{s:ℝ}
def cutA (t:ℝ)(x:E4):ℝ:=Pert.Band.disk (t • x)
def annA (s:ℝ):=cutA s-cutA 1
lemma jetC (s:ℝ): ContDiff ℝ ∞ (cutA s):=Pert.Band.disk.contDiff.comp (f:=fun x:E4=> s • x) (by fun_prop)
lemma ann_ray (s:ℝ):ContDiff ℝ ∞ (annA s):= (jetC s).sub (jetC 1)
lemma romp (hs:0<s)(hx:s⁻¹ ≤ ‖x‖):cutA s x=0:=by apply Pert.Band.disk_out; rw [norm_smul,Real.norm_of_nonneg hs.le]; grw [←hx]; rw [mul_inv_cancel₀ hs.ne']
lemma cage (hs:0<s):HasCompactSupport (cutA s):= HasCompactSupport.intro (isCompact_closedBall (0:E4) s⁻¹) (fun x hx=> romp (x:=x) hs (not_le.mp (fun hy=>hx (mem_closedBall_zero_iff.mpr hy))).le)
lemma cutGlow (s:ℝ): cutA s=ᶠ[𝓝 0] (fun _=>1):=by
    have hv:Tendsto (fun y:E4=>‖s • y‖) (𝓝 0) (𝓝 0):=by simpa using (show Continuous (fun y:E4=>‖s • y‖) by fun_prop).continuousAt (x:=0) |>.tendsto
    exact (hv.eventually (ge_mem_nhds (show (0:ℝ)<1/2 by norm_num))).mono (fun _ hx=>Pert.Band.disk_one hx)
lemma coldA :annA s=ᶠ[𝓝 0] 0:=by filter_upwards [cutGlow s,cutGlow 1] with i hi hk; rw [annA, Pi.sub_apply, hi,hk]; simp
lemma iceAway (g:E4→ℝ)(h:∀ x∈away, ContDiffAt ℝ ∞ g x):ContDiff ℝ ∞ (annA s*g):=by
   rw [contDiff_iff_contDiffAt]; intro x; by_cases hx:x=0; · subst x; exact ContDiffAt.congr_of_eventuallyEq (f:=0) (contDiffAt_const (c:=(0:ℝ))) ((coldA (s:=s)).mono (fun i hi=>by change annA s i*g i=0; change annA s i=0 at hi; rw [hi,zero_mul]))
   exact (ann_ray s).contDiffAt.mul (h x hx)
lemma shipA (hs:0<s): HasCompactSupport (annA s):=(cage hs).sub (cage zero_lt_one)
-- use Leib away for lap of ann.A
lemma Lscl {A:E4→ℝ}(hA:ContDiff ℝ ∞ A)(a:ℝ)(x:E4): lap (fun y=>A (a • y)) x = a^2 * lap A (a • x) :=by
    have he (f:E4→ℝ)(i:Axis): grad i (fun y=> f (a • y))=(a • (fun y=>grad i f (a • y))):=by funext x; unfold grad D; rw [fderiv_comp_smul];rfl
    unfold lap; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [he,grad_smul (show ContDiffAt ℝ ∞ (fun y:E4=> grad i A (a • y)) x from ((grad_diff_all hA i).comp (f:=fun y:E4=> a • y) (by fun_prop)).contDiffAt), he]; change a*(a* _)= _; ring
def bug (s:ℝ)(k:ℕ)(x:E4):= if x∈away then lap (cutA s) x*(rr^k) x +2*∑ i:Axis, grad i (cutA s) x*grad i (rr^k) x else 0
lemma bog (s:ℝ): bug s k =ᶠ[𝓝 0] (fun _=>0):=by
   have hh:= cutGlow s; have hv(i:Axis): grad i (cutA s)=ᶠ[𝓝 0] 0:=by have hx:=grad_won hh i; exact EventuallyEq.trans hx (Eventually.of_forall (fun z=>by simp[grad,D]))
   have hp(i:Axis): grad i (grad i (cutA s))=ᶠ[𝓝 0] 0:=by have hx:= grad_won (hv i) i; exact EventuallyEq.trans hx (Eventually.of_forall (fun z=>by simp [grad,D]))
   filter_upwards [eventually_all.mpr hv,eventually_all.mpr hp] with x hx hg
   dsimp only [bug]; split
   · unfold lap; simp_rw [hg,hx]; simp
   rfl
lemma silk_bug (s:ℝ)(k:ℕ):ContDiff ℝ ∞ (bug s k):=by
    rw [contDiff_iff_contDiffAt]; intro x; by_cases hx:x=0; · subst x; exact ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c:=0)) (bog _)
    let H:= cutA s; let g:= rr^k; have hg:ContDiffAt ℝ ∞ g x:=(rr_smooth hx).pow _; have hb:=jetC s
    have hy:bug s k=ᶠ[𝓝 x] (lap H*g+ (2:ℝ) • ∑ i:Axis, grad i H * grad i g):= by filter_upwards [open_away.mem_nhds (show x∈away from hx)] with y hy; rw [bug,if_pos hy,Pi.add_apply,Pi.smul_apply,Finset.sum_apply]; rfl
    refine (ContDiffAt.add (OPE.lap_diff hb|>.contDiffAt.mul hg) (ContDiffAt.smul (g:=fun y=> (∑ i:Axis, grad i H * grad i g : E4→ℝ) y) (f:=fun _ => (2:ℝ)) contDiffAt_const ?_)).congr_of_eventuallyEq hy
    apply ContDiffAt.congr_of_eventuallyEq (f:= fun y=> ∑ i:Axis, grad i H y * grad i g y) (ContDiffAt.sum (f:=fun i=> fun y=>grad i H y*grad i g y) (fun i _=> (grad_diff_all hb i|>.contDiffAt.mul (grad_smooth_at hg i)))) (Eventually.of_forall fun y=>by simp)
lemma box_bug (hs:0<s):HasCompactSupport (bug s k):=by
    refine HasCompactSupport.intro (cage hs) (fun x hx=>?_)
    have hb:cutA s=ᶠ[𝓝 x] 0:=notMem_tsupport_iff_eventuallyEq.mp hx
    have he(i:Axis): grad i (cutA s)=ᶠ[𝓝 x] 0:=by have hx:=grad_won hb i; exact EventuallyEq.trans hx (Eventually.of_forall (fun z=>by simp [grad,D]))
    rw [bug]; split
    · unfold lap; have hp(i:Axis): grad i (grad i (cutA s)) x=0:=by rw [(grad_won (he i) i).self_of_nhds]; simp [grad,D]
      simp_rw [hp,fun i=> (he i).self_of_nhds]; simp
    rfl
lemma bug_scale (hs:0<s)(k): bug s k x= s^(2*(k+1))* bug 1 k (s • x):=by
   by_cases hx:x=0; · subst x;simp [bug,away]
   have ht:s • x≠ 0:=smul_ne_zero hs.ne' hx
   let P:=s^(2*(k+1))
   have hh : rr (s • x)=s⁻¹^2*rr x:=by unfold rr; rw [norm_smul,Real.norm_of_nonneg hs.le,mul_pow, mul_inv, inv_pow]
   have he: cutA s=(fun y=>cutA 1 (s • y)):= funext fun y=>by simp only[cutA,one_smul]
   simp only [bug,if_pos (show x∈away from hx),if_pos (show s • x∈away from ht)]
   rw [he,Lscl (jetC 1),mul_add]; refine congrArg₂ (·+·) ?_ ?_
   · simp only [Pi.pow_apply,hh,mul_pow]; rw [show 2*(k+1)=2+2*k from by ring, pow_add, pow_mul, inv_pow,inv_pow]; field_simp
   rw [mul_left_comm (_^(_ : ℕ)) (2:ℝ), Finset.mul_sum _ _ (s^(2*(k+1)))]; apply congrArg (fun y:ℝ=> 2*y); apply Finset.sum_congr rfl; intro i _
   rw [grad_power hx, grad_power ht]; rw [show grad i (fun y=>cutA 1 (s • y)) x = s*grad i (cutA 1) (s • x) from by unfold grad D; rw [fderiv_comp_smul];rfl,hh, PiLp.smul_apply,smul_eq_mul,mul_pow,pow_mul, inv_pow,inv_pow]; field_simp
lemma lap_bug (s:ℝ)(k:ℕ): lap (annA s*rr^(k+1))=(4*((k:ℝ)+1)*k) • (annA s*rr^(k+2)) + (bug s (k+1)-bug 1 (k+1)):=by
    funext x; by_cases hx:x=0
    · subst x; have h: (annA s*rr^(k+1))=ᶠ[𝓝 0] 0:=by filter_upwards [coldA (s:=s)] with x hx; simp [hx]
      have ht(i:Axis) : grad i (grad i (annA s*rr^(k+1))) 0=0:=by erw [(grad_won (grad_won h i) i).self_of_nhds]; unfold grad D; simp
      simp only [lap,ht,Finset.sum_const_zero,Pi.add_apply,Pi.smul_apply,Pi.mul_apply,coldA.self_of_nhds,Pi.sub_apply]; simp [bug,away]
    unfold annA; let w:= rr^(k+1); let g:=cutA s; let f:=cutA 1
    have he(i): grad i (cutA s-f)=grad i g-grad i f:=by rw [sub_eq_add_neg,sub_eq_add_neg]; funext x; change grad i (cutA s + -f) x= _; erw [grad_plus ((jetC s).contDiffAt) ((jetC 1).neg.contDiffAt), grad_neg_f]; rfl
    rw [Lp (cutA s - cutA 1) (rr^(k+1)) (hg:=fun x _=> (ann_ray s).contDiffAt) (hf:=fun x hx=>(rr_smooth hx).pow _) (hx:=hx), lap_power hx,lap_sub' (jetC ..) (jetC ..)]; change (lap g x-lap f x)*w x+_+2*(∑ i:Axis,grad i (g-f) x*grad i w x)=_+(bug s (k+1) x-bug 1 (k+1) x)
    simp_rw [show g=cutA s from rfl,he,Pi.sub_apply,Pi.smul_apply, sub_mul,Finset.sum_sub_distrib]; unfold w f g; simp only [bug,if_pos (show x∈away from hx),Pi.mul_apply,Pi.pow_apply,smul_eq_mul,Pi.sub_apply]; ring
end YM.OPE.Sagebrush
