import YM.SchemeConversionRG11.FirstMS.Triad.Vertex

/-! Re-express the projected trident (on separated marks) with jointly soft kernel. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MSbar MeasureTheory Metric Complex DR Maxwell Maxwell.Free Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

variable (h:Bool)(i:Fin 3)(b a μ:Axis)
def sol (t:ℝ)(p:E4):ℝ:= -(grad b (soften t) p)
def soff (h:Bool)(i:Fin 3)(μ:Axis)(t:ℝ)(p:E4):ℝ:=∑ b:Axis,fan h i b μ * sol b t p
def surf (h:Bool)(i:Fin 3)(a μ:Axis)(t:ℝ)(p:E4):ℝ:= grad a (soff h i μ t) p

section business

local notation "safe" p => (p:ℝ × E4) ≠ (0,(0:E4))
lemma refilling (p:ℝ × E4) (hp:safe p): 0< p.1^2+‖p.2‖^2:= by
    by_cases hx:p.2=0; exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (show p.1≠0 from fun h=> hp (Prod.ext h hx))) (sq_nonneg _)
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx))
private lemma division (a:Axis) {f:ℝ → E4 → ℝ}{p:ℝ × E4}(hf:ContDiffAt ℝ ∞ (uncurry f) p):
    ContDiffAt ℝ ∞ (fun p:ℝ × E4=> grad a (f p.1) p.2) p := by
    let F:=fun x:ℝ × E4=> f x.1
    exact (ContDiffAt.fderiv (f:=F) (g:=Prod.snd) (hf.comp (f:=fun v:(ℝ × E4) × E4=> (v.1.1,v.2)) (p,p.2) (by fun_prop)) contDiffAt_snd (by simp : (∞:WithTop ℕ∞)+1≤∞)).clm_apply contDiffAt_const
lemma sol_ok (p:ℝ × E4)(hp:safe p): ContDiffAt ℝ ∞ (uncurry (sol b)) p:= by
    have hf : ContDiffAt ℝ ∞ (uncurry soften) p:=
       contDiffAt_const.mul (((contDiffAt_fst.pow 2).add ((contDiff_norm_sq ℝ).contDiffAt.comp p contDiffAt_snd)).inv (refilling p hp).ne')
    exact (division b hf).neg
lemma soff_ok {p:ℝ × E4}(hp:safe p): ContDiffAt ℝ ∞ (uncurry (soff h i μ)) p:=
    by unfold soff; exact ContDiffAt.sum (s:=Finset.univ) (fun b _=> (contDiffAt_const (c:=fan h i b μ)).mul (sol_ok b p hp))
lemma surf_ok {p:ℝ×E4}(hp:safe p): ContDiffAt ℝ ∞ (uncurry (surf h i a μ)) p:= division a (soff_ok h i μ hp)
lemma surf_value {t:ℝ}{p:E4}(ht:safe (t,p)): surf h i a μ t p = ∑ b:Axis, fan h i b μ * (-grad a (grad b (soften t)) p) := by
    have hm(c:Axis): DifferentiableAt ℝ (fun x=> grad c (soften t) x) p:= by
       suffices hv : DifferentiableAt ℝ (sol c t) p by
          convert! hv.neg using 1; ext1 x; simp only [Pi.neg_apply,sol,neg_neg]
       exact ((sol_ok c (t,p) ht).comp (f:=fun v:E4=>(t,v)) p (by fun_prop)).differentiableAt (by simp)
    unfold surf soff sol
    rw [grad_sum_f]
    · refine Finset.sum_congr rfl fun b _=> ?_
      have he := DFunLike.congr_fun (((hm b).hasFDerivAt.neg.const_mul (fan h i b μ)).fderiv) (basis a)
      exact he.trans (by simp [grad,D]; left; rfl)
    exact fun b _=> (hm b).neg.const_mul _
lemma kernel_real {v:E4} (hv:v≠0) : lane 0 h i μ v 0=↑(soff h i μ 0 v) := by
    unfold lane soff; rw [ofReal_sum]
    have hh : (fun v=> bridge 0 v 0)=ᶠ[𝓝 v] (fun v=> ↑(soften 0 v)) := by
       filter_upwards [eventually_ne_nhds hv] with v hv
       rw [soften_zero]; exact (by simpa [Tree.continued_at_four] using bridge_agrees 0 v hv)
    refine Finset.sum_congr rfl fun b _=> ?_
    rw [ofReal_mul]; congr 1
    unfold base sol grad D; rw [ofReal_neg, hh.fderiv_eq]
    have he : DifferentiableAt ℝ (soften 0) v:= by rw [soften_zero]; exact (freeSmooth hv).differentiableAt (by simp) -- name
    exact congr_arg Neg.neg (DFunLike.congr_fun (ofRealCLM.hasFDerivAt.comp v he.hasFDerivAt).fderiv _)
lemma bar_real {v:E4}(hv:v≠0): bar 0 h i a μ v 0=↑(surf h i a μ 0 v):= by
    have hh : (fun v=> lane 0 h i μ v 0)=ᶠ[𝓝 v] fun v=> (↑(soff h i μ 0 v):ℂ) := (eventually_ne_nhds hv).mono fun v hv=> kernel_real h i μ hv
    unfold bar surf grad D; rw [hh.fderiv_eq]
    have he : DifferentiableAt ℝ (soff h i μ 0) v:=
       ((soff_ok h i μ (p:=(0,v)) (by simp [hv])).comp (f:=fun v:E4=>((0:ℝ),v)) v (by fun_prop)).differentiableAt (by simp)
    exact DFunLike.congr_fun (ofRealCLM.hasFDerivAt.comp v he.hasFDerivAt).fderiv _
end business

end YM.SchemeConversionRG11.FirstMS.Triad
