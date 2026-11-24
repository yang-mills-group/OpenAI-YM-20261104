import YM.SchemeRG11.MSDetector.Kit
/-! Direct FF and FA. Contact read on SAME-helicity in this MSbar IR convention. -/
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
namespace YM.SchemeRG11.MSDetector
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter TopologicalSpace Cluster Steam MSbar Pert Triangle Storm Flare
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace
variable {μ : ℝ} (hμ : 0<μ) (R : ℝ)

noncomputable def near (μ R : ℝ)(J : Gem)(a : Axis) (x : E4) := ∑ i:Axis, coin J i a • MSDetector.pulse μ R [i] 0 x
-- diagonal projected only
noncomputable def peer (μ R : ℝ)(J K : Gem) (x:E4):= -(∑ a, ∑ b, rotatedProduct J.1 J.2 K.1 K.2 a b • MSDetector.pulse μ R [a,b] 0 x)

variable {ι : Type} {v : Filter ι} [v.IsCountablyGenerated]

include hμ
lemma pace (U : Sl){x : E4}(hx:x≠0) : ContinuousAt (fun x=> pulse μ R U 0 x) x := by
  unfold pulse weigh
  refine tendsto_finsetSum _ fun i _=> tendsto_const_nhds.smul ?_
  exact Bubble.score (hemp hμ _) hx _ le_rfl
lemma near_o (J)(a){x}(hx:x≠0): ContinuousAt (near μ R J a) x:= tendsto_finsetSum _ fun i _=> tendsto_const_nhds.smul ((pace hμ R [i] hx):_)
lemma peer_o (J K){x}(hx:x≠0): ContinuousAt (peer μ R J K) x:=by
  unfold peer
  exact Tendsto.neg (tendsto_finsetSum _ fun a _=> tendsto_finsetSum _ fun b _=> tendsto_const_nhds.smul (pace hμ R _ hx))
omit hμ

private lemma heaths (l : Sl) {p : ι→ℝ} (h : Tendsto p v atTop) {x : ι→ E4} {u:E4} (hx:Tendsto x v (𝓝 u)) (hu:u≠0) :
    Tendsto (fun i=>∫ t in Ioc 0 (p i), Steam.tint l t (x i)) v (𝓝 (Steam.score l u)) := by
  rw [Steam.score, ← sculpt l u hu]
  obtain ⟨K,hK,he,hS⟩:=exists_compact_subset isOpen_compl_singleton (show u∈({0}ᶜ:Set _) from hu)
  have hh : ∀ᶠ i in v, x i∈K:= hx.eventually (show ∀ᶠ y in 𝓝 u,y∈K from mem_interior_iff_mem_nhds.mp he)
  obtain ⟨C,hC,c⟩:=costs l hK (fun hi=> hS hi rfl)
  let F i:ℝ→ℝ := (Ioc 0 (p i)).indicator fun t=> Steam.tint l t (x i)
  have ht:= tendsto_integral_filter_of_dominated_convergence (l:=v) (F:=F) (μ:=Zen) (f:=fun t=> Steam.tint l t u) (fun t=>C*Hearth.coat t) (hh.mono fun i hi=> (tint_i l (show x i≠0 from hS hi)).aestronglyMeasurable.indicator measurableSet_Ioc)
    (hh.mono fun i hi=> ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht=> by
       by_cases hu:t∈ Ioc 0 (p i)
       · simpa only [F,indicator_of_mem hu] using c _ hi t ht
       simp only [F,indicator_of_notMem hu,norm_zero]; unfold Hearth.coat; positivity)) (Hearth.pay_coat.const_mul _)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht=> (((series_calm (gauze_diff t) (l.map basis)).continuous.tendsto _).comp hx |>.congr' ((h.eventually (eventually_ge_atTop t)).mono fun i hi=> Eq.symm (indicator_of_mem (show t ∈ Ioc 0 (p i) from ⟨ht,hi⟩) _)))) )
  refine ht.congr fun i=> ?_; unfold F Zen; rw [setIntegral_indicator measurableSet_Ioc,openZen,inter_eq_self_of_subset_right Ioc_subset_Ioi_self]
lemma pulses_go (μ : ℝ)(U : Sl) {p : ι→ℝ} (hp : Tendsto p v atTop){x : ι→E4}{u:E4}(hx:Tendsto x v (𝓝 u))(hu:u≠0) :
    Tendsto (fun i=>pulse μ (p i) U 0 (x i)) v (𝓝 (Complex.ofReal (Steam.score U u))) := by
  simp only [pulse4]; exact lifted (fun i=> Complex.continuous_ofReal.continuousAt.tendsto.comp (heaths U (ends i hp) hx hu))
lemma near_go (μ : ℝ) (J : Gem)(a) {p : ι→ℝ}(hp : Tendsto p v atTop){x : ι→E4}{u:E4}(hx:Tendsto x v (𝓝 u))(hu:u≠0) :
    Tendsto (fun i=> near μ (p i) J a (x i)) v (𝓝 (Complex.ofReal (edge J.1 J.2 a u))) := by
  unfold near edge; push_cast; simp only [coin,Complex.real_smul]; exact tendsto_finsetSum _ (fun i _=> tendsto_const_nhds.mul (pulses_go μ [i] hp hx hu))
lemma peer_paid {μ : ℝ} (J K: Gem){x:E4}(hx:x≠0) : peer μ R J K x=weigh fun i=>Complex.ofReal (∫ t in Ioc 0 (peak R i),fused J.1 J.2 K.1 K.2 t x) := by
  let r := rotatedProduct J.1 J.2 K.1 K.2
  have hi k (a b : Axis): IntegrableOn (fun t=> Steam.tint [a,b] t x*r a b) (Ioc 0 (peak R k)):= (IntegrableOn.mono_set ((tint_i [a,b] hx).mul_const (r a b)) Ioc_subset_Ioi_self)
  have h k : (∫ t in Ioc 0 (peak R k),fused J.1 J.2 K.1 K.2 t x)= -(∑ a,∑ b, r a b * ∫ t in Ioc 0 (peak R k), Steam.tint [a,b] t x) := by
    unfold fused; rw [integral_neg,integral_finsetSum _ (fun a _=>integrable_finsetSum _ fun b _=> hi k a b)] -- maybe reducible
    congr 1; apply Finset.sum_congr rfl; intro a _; rw [integral_finsetSum _ (fun b _=> hi k a b)]; congr 1; ext b; rw [integral_mul_const,mul_comm]
  simp only [peer,pulse4,h,weigh]; push_cast
  simp only [smul_neg, Finset.sum_neg_distrib, Finset.smul_sum,Complex.real_smul]; congr 1
  conv_rhs=> rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro v _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; exact Finset.sum_congr rfl (fun b _ => mul_left_comm ..)
lemma peer_go (μ : ℝ) (i j : Eye) {p : ι→ℝ}(hp:Tendsto p v atTop){x : ι→E4}{u : E4}(hx:Tendsto x v (𝓝 u))(hu:u≠0) :
    Tendsto (fun r=>peer μ (p r) (true,i) (false,j) (x r)) v (𝓝 (Complex.ofReal (mixed i j u))) := by
  unfold peer; rw [mixed_contact _ _ hu]; unfold tensorSum atHessian
  push_cast; simp only [Complex.real_smul]
  refine Tendsto.neg <| tendsto_finsetSum _ (fun a _=> tendsto_finsetSum _ (fun b _=>?_))
  rw [mul_comm]
  exact tendsto_const_nhds.mul (pulses_go _ _ hp hx hu)
end YM.SchemeRG11.MSDetector
