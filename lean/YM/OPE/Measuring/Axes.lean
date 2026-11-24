import YM.OPE.Nesting.Endpoint
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Arbitrarily shrinking ratios inside smooth germs: remove the power slack

Only at corners of a configuration where the relevant readout has a smooth
extension. Bivariate argument permitting polynomial substitutions by paths
of very different depths. Integer multiplication of losses is by the list
length, never a positive lower bound on the ratios. Used first in the special
case of trees bearing at most one elementary slot throughout. This does no gas
or contact analytic continuation at fixed UV mesh.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Measuring.Axes
open Filter Set Function Asymptotics
open scoped ContDiff Topology

variable {E B:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]
variable {f:E→B}{s:Set E}{p:E}

abbrev leaf (v:E) (g:E→B) (x:E):=fderiv ℝ g x v
abbrev path (v:E) (g:E→B) (n:ℕ) := (leaf v)^[n] g
lemma longer (v:E) (g:E→B) (n:ℕ) : path v g (n+1)=leaf v (path v g n):=iterate_succ_apply' ..

lemma leaf_live (v:E) (h:ContDiffAt ℝ ∞ f p) : ContDiffAt ℝ ∞ (leaf v f) p:=by
    exact ((h.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const)
lemma path_live (v:E)(n:ℕ)(h:ContDiffAt ℝ ∞ f p): ContDiffAt ℝ ∞ (path v f n) p :=by
    induction n with
    | zero=>exact h
    | succ n ih=>rw [longer]; exact leaf_live v ih

lemma pair (v w:E)(h:ContDiffAt ℝ ∞ f p): leaf v (leaf w f) p = leaf w (leaf v f) p:=by
    have ht (u q:E): leaf u (leaf q f) p=fderiv ℝ (fderiv ℝ f) p u q:=by
       change fderiv ℝ (fun y : E=> (fderiv ℝ f y) ((fun _:E=>q) y)) p u = _
       rw [fderiv_clm_apply ((h.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)) (differentiableAt_const q)]; simp
    simp_rw [ht]; exact h.isSymmSndFDerivAt (by norm_num; exact WithTop.coe_le_coe.mpr (le_top (a:=(2:ℕ∞)))) v w
lemma inversePath (v w:E)(n:ℕ)(h:∀ᶠ x in 𝓝 p, ContDiffAt ℝ ∞ f x): leaf v (path w f n) p=path w (leaf v f) n p:=by
    induction n generalizing p with
    | zero=>rfl
    | succ n ih=>
       rw [longer,pair _ _ (path_live w n h.self_of_nhds), longer _ _ n]
       refine congr_arg (fun (q:E→L[ℝ]B)=>q w) (EventuallyEq.fderiv_eq (𝕜:=ℝ) ?_)
       -- step commutes on a smooth neighborhood
       filter_upwards [eventually_eventually_nhds.mpr h] with x hx using ih hx

lemma affine_deriv (v:E){t:ℝ}(h:DifferentiableAt ℝ f (p+t•v)): HasDerivAt (fun z:ℝ=>f (p+z•v)) (leaf v f (p+t•v)) t:=by
    apply h.hasFDerivAt.comp_hasDerivAt t (f:=fun z:ℝ=>p+z•v) ?_
    exact (hasDerivAt_const t p).add ((hasDerivAt_id' t).smul_const v)|>.congr_deriv (by simp)
lemma path_affine (v:E)(n:ℕ) {t:ℝ}(h:∀ᶠ x in 𝓝 (p+t•v), ContDiffAt ℝ ∞ f x): path v f n (p+t•v)=iteratedDeriv n (fun z:ℝ=>f (p+z•v)) t:=by
    induction n generalizing t with
    | zero=>rfl
    | succ n ih=>
       rw [iteratedDeriv_succ, ← Filter.EventuallyEq.deriv_eq (f:=iteratedDeriv n (fun z:ℝ=>f (p+z•v))) (f₁:=fun z:ℝ=>path v f n (p+z•v)) (?_), longer]
       exact (affine_deriv _ ((path_live v n h.self_of_nhds).differentiableAt (by simp))).deriv.symm
       filter_upwards [(show ContinuousAt (fun z:ℝ=>p+z•v) t from (continuous_const.add (continuous_id.smul continuous_const)).continuousAt).tendsto.eventually (eventually_eventually_nhds.mpr h)] with t h using ih h

-- positive one-sided rate along any direction strictly past the preceding integer power
lemma pre_jets {n:ℕ}{v:E}{a C:ℝ}(ha: (n:ℝ) < a)(h:∀ᶠ q in 𝓝 p, ContDiffAt ℝ ∞ f q) (hF:∀ᶠ t:ℝ in 𝓝[>]0, ‖f (p+t•v)‖ ≤ C* t^a): path v f n p=0 := by
    have hlim : Tendsto (fun z:ℝ=>p+z•v) (𝓝 0) (𝓝 p):=by convert (show Continuous (fun z:ℝ=>p+z•v) from continuous_const.add (continuous_id.smul continuous_const)).continuousAt.tendsto; simp
    have hh:=hlim.eventually h; let g(z:ℝ):=f (p+z•v)
    obtain ⟨r,hr,hw⟩:= (Metric.nhds_basis_ball.eventually_iff).mp hh
    let S:=Icc (0:ℝ) (r/2)
    have hw': ContDiffOn ℝ ∞ g S:= by
       intro t ht; refine ((hw ?_).comp t (𝕜:=ℝ) (g:=f) (f:=fun z:ℝ=>p+z•v) (by fun_prop)).contDiffWithinAt; rw [Metric.mem_ball,dist_zero_right,Real.norm_of_nonneg ht.1]; exact ht.2.trans_lt (half_lt_self hr)
    have hle : 𝓝[>]0 ≤ 𝓝[S]0 := le_inf nhdsWithin_le_nhds <| le_principal_iff.mpr <| ((eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds (half_pos hr))).and (self_mem_nhdsWithin (s:=Ioi (0:ℝ)))).mono fun _ h=> ⟨h.2.le,h.1⟩
    have H(k:ℕ)(hk : (k:ℝ)<a): Tendsto (fun t:ℝ=>(t^k)⁻¹ • g t) (𝓝[>]0) (𝓝 0):= by
       apply Metric.tendsto_nhds.mpr ?_; intro ε hε; have he:=sub_pos.mpr hk; filter_upwards [(nhdsWithin_le_nhds (s:=Ioi (0:ℝ))) ((continuousAt_const.mul (Real.continuousAt_rpow_const (0:ℝ) (a-(k:ℝ)) (Or.inr he.le))).tendsto.eventually (gt_mem_nhds (show C*(0:ℝ)^(a-(k:ℝ))< ε by rw [Real.zero_rpow he.ne',mul_zero]; exact hε))),hF,self_mem_nhdsWithin] with t ht hF hp; change 0<t at hp
       rw [dist_zero_right,norm_smul,Real.norm_of_nonneg (by positivity)]; exact (mul_le_mul_of_nonneg_left hF (inv_nonneg.mpr (pow_nonneg hp.le _))).trans_lt (by change C*t^(a-(k:ℝ))<ε at ht; rw [Real.rpow_sub hp,Real.rpow_natCast,div_eq_mul_inv] at ht; linarith only [ht])
    have ht' (k:ℕ)(hk:k≤n): Tendsto (fun t:ℝ=>(t^k)⁻¹ • taylorWithinEval g k S 0 t) (𝓝[>]0) (𝓝 0):= by
       have hh : (fun t=>g t-taylorWithinEval g k S 0 t) =o[𝓝[S]0] (fun t=>t^k):= by simpa only [sub_zero] using taylor_isLittleO (convex_Icc _ _) (show (0:ℝ)∈S from ⟨le_rfl, le_of_lt (half_pos hr)⟩) (hw'.of_le (WithTop.coe_le_coe.mpr (le_top (a:=(k:ℕ∞)))))
       have hsub : Tendsto (fun t:ℝ=>(t^k)⁻¹ • (g t-taylorWithinEval g k S 0 t)) (𝓝[>]0) (𝓝 0):= by
          refine Metric.tendsto_nhds.mpr fun ε he=> ?_; filter_upwards [hle (hh.def (half_pos he)),self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with t ht hp; change 0<t at hp
          have hx:= mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr (pow_nonneg hp.le k)); rw [Real.norm_of_nonneg (pow_nonneg hp.le k)] at hx; rw [dist_zero_right,norm_smul,Real.norm_of_nonneg ((inv_nonneg.mpr (pow_nonneg hp.le k)))]; field_simp [pow_ne_zero _ hp.ne'] at hx ⊢; nlinarith only [hx, mul_pos he (pow_pos hp k)]
       have hZ:= (H k ((show (k:ℝ) ≤ n from by exact_mod_cast hk) |>.trans_lt ha)).sub hsub; simp_rw [smul_sub, sub_sub_cancel, sub_zero] at hZ; exact hZ
    have hv(k:ℕ)(hk:k≤ n): iteratedDeriv k g 0=0 ∧ ∀ t, taylorWithinEval g k S 0 t=0 := by
       induction k with
       | zero=>
          have hg:ContDiffAt ℝ ∞ g (0:ℝ) := by
             exact ((hh.self_of_nhds).comp 0 (g:=f) (by fun_prop))
          have hlim := H 0 (show (↑(0:ℕ):ℝ)<a from by simpa only [Nat.cast_zero] using ((Nat.cast_nonneg n).trans_lt ha)); simp only [pow_zero,inv_one,one_smul] at hlim; have hD:=tendsto_nhds_unique (l:=𝓝[>] (0:ℝ)) (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlim
          exact ⟨by rw [iteratedDeriv_zero]; exact hD, fun t=>by rw [taylor_within_zero_eval]; exact hD⟩
       | succ k ih=>
          have hj(t:ℝ): taylorWithinEval g (k+1) S 0 t = ((t)^(k+1)) • ((((↑(Nat.factorial (k+1)):ℝ)⁻¹) • (iteratedDeriv (k+1) g 0))) :=by
             rw [taylorWithinEval_succ,(ih (by omega)).2 t,zero_add,sub_zero,smul_smul,iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (half_pos hr))]
             · rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]; rw [mul_comm]
             · exact ((hh.self_of_nhds).comp 0 (g:=f) (by fun_prop)).of_le (WithTop.coe_le_coe.mpr (le_top (a:=((k+1:ℕ):ℕ∞))))
             exact ⟨le_rfl,le_of_lt (half_pos hr)⟩
          have he:=ht' (k+1) hk; have hc:=tendsto_nhds_unique (f:=fun _=>_) (l:=𝓝[>] (0:ℝ)) (a:=((↑(Nat.factorial (k+1)):ℝ)⁻¹ • iteratedDeriv (k+1) g 0)) tendsto_const_nhds (he.congr' ?_); swap
          · filter_upwards [self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with t ht; rw [hj t, inv_smul_smul₀ (pow_ne_zero _ ht.ne')]
          have hD: iteratedDeriv (k+1) g 0=0:= (smul_eq_zero.mp hc).resolve_left (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (k+1)))
          exact ⟨hD,fun t=>by rw [hj,hD,smul_zero,smul_zero]⟩
    have hh':iteratedDeriv n (fun z:ℝ=>f (p+z•v)) (0:ℝ)=0:=by exact (hv n le_rfl).1
    simpa only [zero_smul,add_zero,hh'] using path_affine (f:=f) v n (p:=p) (t:=0) (by simpa using h)
end YM.OPE.Measuring.Axes
