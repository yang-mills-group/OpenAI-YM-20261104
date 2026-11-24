import YM.Pert.Fourier.Return
/-!
# Dilation multi-division. Joint symbol downshifts
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function Filter Lattice MeasureTheory Set Topology Metric
open scoped BigOperators Classical ContDiff Matrix
variable {M E F:Type*}
def crimp {M α:Type*}[Sub M][SMul ℝ M](s:ℝ)(v:α→α): ℕ→(α→ M)→α→M
 | 0,a,x=>a x
 | k+1,a,x=>crimp s v k a x-s^k • crimp s v k a (v x)
variable [NormedAddCommGroup M][NormedSpace ℝ M] [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F]{s t:ℝ}{k i:ℕ}
abbrev chill (s:ℝ)(i:ℕ)(f:ℝ→M) := crimp s (· / s) i f
abbrev glide {M:Type*}[Sub M][SMul ℝ M](s:ℝ)(i:ℕ)(f:ℕ→M) := crimp s (· +1) i f
lemma starMem {s t a:ℝ} (hs:1 ≤ s)(hp:a∈ Icc 0 t):a/s∈ Icc 0 t:=by
   have hx:0 ≤ t:=le_trans hp.1 hp.2; have hh:0<s:=zero_lt_one.trans_le hs; refine ⟨div_nonneg hp.1 hh.le,(div_le_iff₀ hh).mpr ?_⟩; apply hp.2.trans; exact le_mul_of_one_le_right hx hs
lemma iceC (hk:k>0)(f:ℝ→M): chill s k f 0=0:=by
   induction k with
   | zero=>omega
   | succ k ih=>cases k with | zero=>simp [chill,crimp] | succ _=>change chill s _ _ _-_•chill s _ _ (0/s)=0; rw [zero_div, ih (by omega)];simp
lemma stir {f g:ℝ→M}(hs:1 ≤ s){x:ℝ}(hv:x∈ Icc 0 t) (hp:∀ u∈ Icc 0 t, HasDerivAt f (g u) u): HasDerivAt (chill s (k+1) f) (chill s k (fun u=> g u-s⁻¹ • g (u/s)) x) x:=by
   have hh:0<s:=zero_lt_one.trans_le hs; induction k generalizing x with
   | zero=>
     have he:HasDerivAt (f ∘ (· /s)) ((1/s)•g (x/s)) x:= HasDerivAt.scomp _ (hp (x/s) (starMem hs hv)) ((hasDerivAt_id' x).div_const s)
     have hf:= (hp x hv).sub he; simpa only [chill,crimp,one_div,comp_def,Pi.sub_apply,pow_zero,one_smul] using! hf
   | succ j ih=>
     let F : ℝ→ M:=chill s j (fun u=> g u-s⁻¹ • g (u/s)); have he:HasDerivAt ((chill s (j+1) f) ∘ (· /s)) ((1/s)•F (x/s)) x:= HasDerivAt.scomp _ (ih (starMem hs hv)) ((hasDerivAt_id' x).div_const s)
     have hf:= (ih hv).sub (he.const_smul (s^(j+1))); rw [smul_smul (s^(j+1):ℝ),pow_succ, mul_assoc, one_div, mul_inv_cancel₀ (ne_of_gt hh),mul_one] at hf -- pow_succ rewrites function too
     simpa only [comp_def,chill,crimp, F,pow_succ] using! hf
lemma snow {g:ℝ→ E→F}{X:Set E}(hs:1 ≤ s)(hp:IsCompact X)(H:∀ z∈ (Icc 0 t ×ˢ X), ContDiffAt ℝ ∞ (Function.uncurry g) z) : ∃ C≥0,∀ z∈ X,∀ x∈ Icc 0 t, ‖chill s k (fun u=>g u z) x‖ ≤ x^k*C:=by
   induction k generalizing g with
   | zero=>
     obtain ⟨C,hC⟩:=(isCompact_Icc.prod hp).exists_bound_of_continuousOn (fun z hz=> (H z hz).continuousAt.continuousWithinAt)
     exact ⟨max C 0,le_max_right ..,fun z hz x hx=>by simpa only [pow_zero,one_mul] using! (hC (x,z) ⟨hx,hz⟩).trans (le_max_left ..)⟩
   | succ k ih=>
     let A:=fun z:E=>fun x => g x z; let g':=fun u z=>deriv (A z) u
     have hg(z:ℝ×E)(hz:z∈(Icc 0 t ×ˢ X)): ContDiffAt ℝ ∞ (Function.uncurry g') z:=by
        have hw:= (H z hz).comp (f:=fun p:(ℝ×E)×ℝ=> (p.2,p.1.2)) (z,z.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
        exact ((ContDiffAt.fderiv (f:=fun v y=> A v.2 y) (g:=Prod.fst) hw (contDiffAt_fst (𝕜:=ℝ)) (m:=∞) (by simp)).clm_apply (contDiffAt_const (𝕜:=ℝ) (c:=1)))
     let g₂(u z):= g' u z - s⁻¹ • g' (u/s) z; obtain ⟨C,hC,H'⟩:= ih (g:=g₂) (fun z hz=> (hg z hz).sub (((hg (z.1/s,z.2) ⟨starMem hs hz.1,hz.2⟩).comp (f:=fun p:ℝ×E=> (p.1/s,p.2)) z (by fun_prop)).const_smul (s⁻¹)))
     have hh(z)(hz:z∈X)(x:ℝ)(hx:x∈Icc 0 t):HasDerivAt (chill s (k+1) (A z)) (chill s k (fun u=> g₂ u z) x) x:=stir (g:=fun u=>g' u z) hs hx (fun y hy=> ((show ContDiffAt ℝ ∞ (A z) y from (H (y,z) ⟨hy,hz⟩).comp (f:=fun u=>(u,z)) y (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)).hasDerivAt)
     refine ⟨C,hC,fun z hz x hx=>?_⟩
     have ht(y:ℝ)(hy:y∈Icc 0 x):y∈ Icc 0 t:=⟨hy.1,le_trans hy.2 hx.2⟩
     have hv:= Convex.norm_image_sub_le_of_norm_deriv_le (𝕜:=ℝ) (f:=chill s (k+1) (A z)) (C:=x^k*C) (fun y hy=>(hh z hz y (ht y hy)).differentiableAt) (fun y hy=> ?_) (convex_Icc 0 x) (show (0:ℝ)∈Icc 0 x from ⟨le_rfl,hx.1⟩) (show x∈Icc 0 x from ⟨hx.1,le_rfl⟩)
     rotate_left
     · rw [(hh z hz y (ht y hy)).deriv]; exact (H' z hz y (ht y hy)).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy.1 hy.2 k) hC)
     rw [iceC (by omega),sub_zero, sub_zero, Real.norm_of_nonneg hx.1,mul_right_comm] at hv; exact hv
end YM.OPE.Balsam
