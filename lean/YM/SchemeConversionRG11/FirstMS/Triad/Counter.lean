import YM.SchemeConversionRG11.FirstMS.Triad.SameHand

/-! Annular value zero of opposite helicity distribution. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MeasureTheory Metric Complex DR Maxwell Maxwell.Free Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable (i m:Fin 3) {t:ℝ} (ht:0<t)
include ht
private def H(t:ℝ)(a c:Axis)(v:E4):= grad a (grad c (soften t)) v
private theorem subZ (D:ℝ) (a c:Axis)(hk:c≠a) : (∫ v in closedBall (0:E4) D,H t a c v)=0 := by
   let P : ∀ _ : Axis, ℝ ≃ₗᵢ[ℝ] ℝ:= fun i => if i=a then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ _
   let L:= LinearIsometryEquiv.piLpCongrRight 2 P
   have he(v:E4): H t a c (L v)= -H t a c v:= by
      have hz : basis a c=0:= by simp [basis_eq,hk]
      have ha(v:E4):0<t^2+‖v‖^2:=by positivity
      unfold H; rw [soften_second (ha _).ne',soften_second (ha _).ne', hz, L.norm_map]
      simp only [L,LinearIsometryEquiv.piLpCongrRight_apply,P,hk, ↓reduceIte, WithLp.ofLp_toLp]; rw [show LinearIsometryEquiv.neg ℝ (v a)= -v a from rfl,show LinearIsometryEquiv.refl ℝ ℝ (v c)= v c from rfl]; ring
   let f(v:E4):= (closedBall (0:E4) D).indicator (H t a c) v
   have hx(v): f (L v)=-f v:=by
      unfold f indicator; have hy : L v∈closedBall (0:E4) D↔v∈closedBall (0:E4) D:=by simp
      split_ifs with h h <;> first | exact he _ | simp_all
   suffices hh:(∫ v,f v)=-(∫ v,f v) by unfold f at hh; rw [integral_indicator (isClosed_closedBall.measurableSet)] at hh; linarith
   nth_rw 1 [← L.measurePreserving.integral_comp L.toHomeomorph.measurableEmbedding]; simp_rw [hx]; exact integral_neg _
private theorem mainZ (D:ℝ) (a c:Axis): (∫ v in closedBall (0:E4) D,H t a a v)=∫ v in closedBall (0:E4) D,H t c c v:= by
   let P:=Equiv.swap a c
   let L:=LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ P
   have he(v:E4):H t a a (L v)= H t c c v:= by
      unfold H; have ha(v:E4):0 < t^2+‖v‖^2:= by positivity
      rw [soften_second (ha _).ne',soften_second (ha _).ne',L.norm_map,show (L v) a=v c from ?_]
      · simp [basis_eq]
      unfold L; rw [LinearIsometryEquiv.piLpCongrLeft_apply]; simp [P]
   rw [←integral_indicator measurableSet_closedBall,← L.measurePreserving.integral_comp L.toHomeomorph.measurableEmbedding]
   refine Eq.trans (b:=∫ v,(closedBall (0:E4) D).indicator (H t c c) v) ?_ (integral_indicator measurableSet_closedBall)
   refine integral_congr_ae (Eventually.of_forall fun v=>?_)
   unfold indicator; dsimp only
   simp [he]
lemma clear_zero (D:ℝ)(z:E4): (∫ w in closedBall z D, clasp true i false m t (w-z))=0:= by
   have hi(v:E4): (t,v)≠0:= fun hh=>ht.ne' (congrArg Prod.fst hh)
   let B:=closedBall (0:E4) D
   have he : (∫ w in closedBall z D, clasp true i false m t (w-z))=∫ v in B, clasp true i false m t v:= by
      rw [← integral_indicator measurableSet_closedBall, ← integral_add_right_eq_self _ z]
      refine Eq.trans (integral_congr_ae (g:=B.indicator (clasp true i false m t)) (Eventually.of_forall fun v=>?_)) (integral_indicator measurableSet_closedBall); simp [B,indicator]
   rw [he]; simp_rw [clasp_sum true i false m (hi _), integral_neg]
   change -(∫ v in B,∑ c:Axis,∑ a:Axis,H t a c v*rawProduct i m c a)=_
   have hd(a c:Axis): IntegrableOn (fun v=> H t a c v*rawProduct i m c a) B:= by
      apply Integrable.mul_const
      exact ((gradient_smooth (gradient_smooth ((soften_diff ht).of_le (m:=∞) le_top) c) a).continuous).continuousOn.integrableOn_compact (isCompact_closedBall ..)
   rw [integral_finsetSum _]; swap; · exact fun i _=> integrable_finsetSum _ (fun k _=> hd k i)
   simp_rw [integral_finsetSum _ (fun j _=>hd j _),integral_mul_const]
   let Z:=(∫ v in B,H t 0 0 v)
   have hh(c:Axis): (∑ a:Axis,(∫ v in B,H t a c v)*rawProduct i m c a)=Z*rawProduct i m c c:=by rw [Finset.sum_eq_single_of_mem c (Finset.mem_univ _) (fun a _ ha=> by rw [subZ ht D _ _ (Ne.symm ha),zero_mul]),mainZ ht D c 0]
   simp_rw [hh,← Finset.mul_sum,trace_rule,mul_zero,neg_zero]

omit ht in
lemma mixed_negative {w:E4}(hw:w≠0): mixed i m (-w)=mixed i m w:= by
    have he := mixed_rays i m|>.stretch hw (by norm_num : -(1:ℝ)≠0)
    norm_num at he; exact he

lemma clasp_smooth (b d:Bool): ContDiff ℝ ∞ (clasp b i d m t):= by
    refine contDiff_iff_contDiffAt.mpr fun z=> ContDiffAt.sum fun a _=> ContDiffAt.sum fun c _=>?_
    exact contDiffAt_const.mul ((surf_ok b i a c (p:=(t,z)) (by simp [ht.ne'])).comp (f:=fun z:E4=> (t,z)) z (by fun_prop))

end YM.SchemeConversionRG11.FirstMS.Triad
