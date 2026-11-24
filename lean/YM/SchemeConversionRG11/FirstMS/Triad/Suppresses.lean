import YM.SchemeConversionRG11.FirstMS.Triad.Eaves

/-! Kernel soft trident is genuinely Lebesgue-integrable and has the local-IBP limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MSbar MeasureTheory Metric Complex DR Maxwell Maxwell.Free Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

variable (x:Nodes)(l:P→Stem)(j:P)(a:Axis) {R:ℝ}
variable {χ:E4→ℝ} (hc:ContDiff ℝ ∞ χ)(hp:HasCompactSupport χ)
variable (he:∀ i,i≠j → x i ∉ tsupport χ) (hf:χ=ᶠ[𝓝 (x j)] fun _=>1)

lemma leg_gradient (t:ℝ)(w:E4): grad a (leg x l t j) w=surface x l j a t w:= by
   unfold leg surface surf grad D; rw [fderiv_comp_sub] -- lemma

include hc hp he

def piece (χ:E4→ℝ)(t:ℝ)(v:E4):= χ v*bypass x l j t v

omit hp in
lemma piece_smooth : ContDiff ℝ ∞ (uncurry (piece x l j χ)) := by
   rw [contDiff_iff_contDiffAt]; intro z; by_cases hx : z.2∈tsupport χ
   · apply (hc.comp contDiff_snd|>.contDiffAt).mul (bypass_smooth x l j (v:=z.2) (t:=z.1) fun i hi=> Or.inr ?_)
     exact fun h=>he i hi (h ▸ hx)
   apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
   filter_upwards [continuousAt_snd.tendsto.eventually (notMem_tsupport_iff_eventuallyEq.mp hx)] with w hw
   change χ w.2 * _=0; rw [show χ w.2=0 from hw,zero_mul]

omit hp in
lemma piece_deriv : ContDiff ℝ ∞ (fun p:ℝ×E4=> grad a (piece x l j χ p.1) p.2):= by
   apply contDiff_iff_contDiffAt.mpr; intro t
   exact (ContDiffAt.fderiv (f:=fun p:ℝ×E4=>piece x l j χ p.1) (g:=Prod.snd)
     ((piece_smooth x l j hc he).contDiffAt.comp (f:=fun p : (ℝ×E4) × E4=> (p.1.1,p.2)) (t,t.2) (by fun_prop)) contDiffAt_snd (by simp : (∞:WithTop ℕ∞)+1≤∞)).clm_apply contDiffAt_const

omit hc hp he in
lemma mobile (t:ℝ) {v:E4}(hv:v∉tsupport χ): grad a (piece x l j χ t) v=0:= by
   have hh : piece x l j χ t =ᶠ[𝓝 v] fun _=> 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hv] with v hv
      rw [piece,show χ v=0 from hv,zero_mul]
   unfold grad D; rw [hh.fderiv_eq]; simp

omit he in
lemma covered {t:ℝ}(ht:0<t): Integrable (fun v=> χ v*softsphere x l j a t v):=
   (hc.continuous.mul (all_smooth x l j a ht|>.continuous)).integrable_of_hasCompactSupport hp.mul_right

lemma pushes {t:ℝ}(ht:0<t):
    (∫ v,χ v*softsphere x l j a t v)=-∫ v,leg x l t j v*grad a (piece x l j χ t) v := by
   let g:= piece x l j χ t; let f:= leg x l t j
   rw [show (fun v=>χ v*softsphere x l j a t v)= fun v=> g v*grad a f v from ?_]; swap
   · ext1 v; rw [show grad a f v=surface x l j a t v from leg_gradient ..]; dsimp only [g,piece, softsphere]; ring
   have hd: ContDiff ℝ ∞ g := (piece_smooth x l j hc he).comp (contDiff_const.prodMk contDiff_id)
   have hs: HasCompactSupport g:= hp.mul_right
   have hD : ContDiff ℝ ∞ f := contDiff_iff_contDiffAt.mpr fun v=> (leg_smooth x l j (v:=v) (t:=t) (Or.inl ht.ne')).comp (f:=fun v => (t,v)) v (by fun_prop)
   rw [show (fun v=>leg x l t j v*grad a g v)=(fun v=> grad a g v*f v) from funext fun v=> mul_comm ..]
   have hh := ((gradient_smooth hd a).continuous.mul hD.continuous).integrable_of_hasCompactSupport (μ:=volume) (gradient_small hs a|>.mul_right (f':=f)) -- arg
   exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hh ((hd.continuous.mul (gradient_smooth hD a).continuous).integrable_of_hasCompactSupport hs.mul_right) ((hd.continuous.mul hD.continuous).integrable_of_hasCompactSupport hs.mul_right) (fun v _=> hd.differentiable (by simp) v) (fun v _=> hD.differentiable (by simp) v)

lemma dampens :
    let D(t:ℝ)(v:E4):= leg x l t j v*grad a (piece x l j χ t) v
    Integrable (D 0) ∧ Tendsto (fun t=> ∫ v, D t v) (𝓝[>] 0) (𝓝 (∫ v,D 0 v)):=by
   intro D
   let K:=tsupport χ
   have hh:= piece_deriv x l j a hc he
   obtain ⟨B,hB⟩:=(isCompact_Icc (a:=(0:ℝ)) (b:=1)).prod hp |>.exists_bound_of_continuousOn hh.continuous.continuousOn
   obtain ⟨Q,H,h⟩:=leg_local x l j
   have hK : MeasurableSet K:= isClosed_closure.measurableSet
   have hm := ((H.integrableOn_isCompact hp).integrable_indicator hK).mul_const (|B|)
   have hx(t)(ht:t∈ Icc (0:ℝ) 1): ∀ᵐ v:E4, ‖D t v‖ ≤ K.indicator Q v*|B|:= by
      filter_upwards [h t] with v hv
      by_cases hy:v∈K
      · rw [indicator_of_mem hy]; exact le_trans (norm_mul_le ..) (mul_le_mul hv ((hB (t,v) ⟨ht,hy⟩).trans (le_abs_self _)) (norm_nonneg _) ((norm_nonneg _).trans hv)) -- mul_le last? B is ‖second‖ y? check
      unfold D; rw [mobile x l j a  _ hy,mul_zero,norm_zero,indicator_of_notMem hy,zero_mul]
   have hv'(t:ℝ): AEStronglyMeasurable (D t) volume:=
      ((measurable_of_continuousOn_compl_singleton (x j) (f:=leg x l t j) (fun v hv=> ((leg_smooth x l j (t:=t) (v:=v) (Or.inr hv)|>.continuousAt).comp (f:=fun v:E4=> (t,v)) (by fun_prop)).continuousWithinAt)).mul (hh.continuous.comp (f:=fun v:E4=> (t,v)) (by fun_prop)|>.measurable)).aestronglyMeasurable
   refine ⟨hm.mono' (hv' 0) (hx _ (left_mem_Icc.mpr (by norm_num))),tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall hv') ?_ hm ?_⟩
   · filter_upwards [self_mem_nhdsWithin,eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (show (0:ℝ)<1 from one_pos))] with v hv hy; exact hx v ⟨(Set.mem_Ioi.mp hv).le,(by exact le_of_lt hy)⟩ -- fix shadow
   filter_upwards [volume.ae_ne (x j)] with v hv
   exact ((leg_smooth x l j (t:=0) (v:=v) (Or.inr hv)|>.continuousAt|>.mul (hh.continuous.continuousAt)).comp (f:=fun t:ℝ=>(t,v)) (by fun_prop)).continuousWithinAt

include hf
omit he in
lemma integrates_smooth (h:x∈conf 3) (t:ℝ)(ht:0<t): Integrable (softsphere x l j a t):= by
   have H := ((exterior x l j a hc.continuous hp hf h).1 t).add (covered x l j a hc hp ht)
   apply H.congr; exact Eventually.of_forall fun v=> show (1-χ v)*_+_*softsphere _ _ _ _ _ _=_ from (by ring)

lemma bills (h:x∈conf 3):
    Tendsto (fun t=> ∫ v:E4, softsphere x l j a t v) (𝓝[>] (0:ℝ))
        (𝓝 ((∫ v:E4,(1-χ v)*softsphere x l j a 0 v)-(∫ v:E4,leg x l 0 j v*grad a (piece x l j χ 0) v))) := by
    have he':= exterior x l j a hc.continuous hp hf h
    apply (he'.2.sub (dampens x l j a hc hp he).2).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [sub_eq_add_neg,← pushes x l j a hc hp he (show 0<t from ht),← integral_add (he'.1 t) (covered x l j a hc hp ht)]
    refine integral_congr_ae (Eventually.of_forall fun v=> ?_)
    ring

end YM.SchemeConversionRG11.FirstMS.Triad
