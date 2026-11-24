import YM.SchemeConversionRG11.FirstMS.Triad.Knee

/-! Soft regulator collapse in projected integrated trident. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MeasureTheory Metric Complex DR Maxwell Maxwell.Free Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {x:Nodes}{R ρ:ℝ}(h:Box x R ρ)(l:P→Stem)(j:P)(p:Bool)(m:Fin 3)

section edge
-- soft segment split holds for each stem world even j moved.
include h
variable {χ:E4→ℝ} (hc:Continuous χ)(hp:HasCompactSupport χ)(hw:χ =ᶠ[𝓝 (x j)] fun _=>1)

include hc hp hw
lemma shot_external :
   let Q(t:ℝ)(w:E4) := (1-χ w)*shot (x:=x) l j p m t w
   (∀ t:ℝ,Integrable (Q t)) ∧ Tendsto (fun t=>∫ w,Q t w) (𝓝[>] 0) (𝓝 (∫ w,Q 0 w)):=by
   intro Q
   let F(a b:Axis)(t:ℝ)(w:E4):= (1-χ w)*softsphere x (incline j l b) j a t w
   have hf(a b:Axis)(t:ℝ): Integrable (fun w=>fan p m a b * F a b t w):=((exterior x _ _ _ hc hp hw h.confirms).1 t).const_mul _
   have he(t) : Q t= fun w:E4=>∑ a:Axis,∑ b:Axis,fan p m a b*F a b t w:= by
      funext w; unfold Q F shot; rw [live_signal]; simp only [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _=>Finset.sum_congr rfl fun b _=> mul_left_comm ..
   have hv(a:Axis)(t:ℝ) := integrable_finsetSum Finset.univ (fun b _=> hf a b t)
   refine ⟨fun t=> ?_,?_⟩
   · rw [he]; exact integrable_finsetSum _ fun a _=> hv a t
   simp_rw [he, integral_finsetSum _ (fun _ _=> hv _ _), integral_finsetSum _ (fun _ _=> hf _ _ _),integral_const_mul]
   exact tendsto_finsetSum _ fun a _=> tendsto_finsetSum _ fun b _=> ((exterior x (incline j l b) j a hc hp hw h.confirms).2.const_mul _)
lemma shot_follows {g:ℝ} (hi: Tendsto (fun t=> ∫ w, χ w*shot (x:=x) l j p m t w) (𝓝[>] 0) (𝓝 g)) :
    Tendsto (fun t=>∫ w,shot (x:=x) l j p m t w) (𝓝[>] 0) (𝓝 ((∫ w:E4,(1-χ w)*shot (x:=x) l j p m 0 w)+g)):= by
   have hx:= shot_external h l j p m hc hp hw
   refine (hx.2.add hi).congr' ?_
   filter_upwards [self_mem_nhdsWithin] with t ht
   have he: Continuous (shot (x:=x) l j p m t):= by
      change Continuous (fun v=> clasp (l j).dual (l j).i p m t (v-x j)*bypass x l j t v)
      simp_rw [live_signal]
      exact continuous_finsetSum _ (fun a _=> continuous_finsetSum _ (fun b _=> (all_smooth x (incline j l b) j a ht).continuous.const_mul _))
   rw [← integral_add (f:=fun v=>(1-χ v)*shot (x:=x) l j p m t v) (g:=fun v=>χ v*shot (x:=x) l j p m t v) (hx.1 t) ((hc.mul he).integrable_of_hasCompactSupport hp.mul_right)]
   exact integral_congr_ae (Eventually.of_forall fun w:E4=>show (1-_)*shot l j p m t w+_*_=shot (x:=x) l j p m t w from by ring)

omit h hc hp hw in
lemma absorbing (b:ℝ× E4→ℝ)(he:Continuous b) {K:Set E4}(hK:IsCompact K)(hb:∀ t,∀ v∉K,b (t,v)=0) : -- reusable, independence h later
   Tendsto (fun t:ℝ=>∫ v:E4, source t (v-x j)*b (t,v)) (𝓝[>] 0) (𝓝 (b (0,x j))) := by
   let f(t:ℝ)(v:E4):= source 1 v*b (t,x j + t • v)
   have hv(t:ℝ)(ht:0<t) : (∫ v:E4, source t (v-x j)*b (t,v))=∫ v,f t v:= by
      rw [dilate_integral (fun v:E4=> source t (v-x j)*b (t,v)) (x j) t ht,← integral_smul]
      apply integral_congr_ae; exact Eventually.of_forall fun v=>by dsimp only; rw [add_sub_cancel_left,smul_eq_mul,← mul_assoc,source_scale ht]
   obtain ⟨C,hC⟩:= ((isCompact_Icc (a:=(0:ℝ)) (b:=1)).prod hK).exists_bound_of_continuousOn he.continuousOn
   have ht(t:ℝ)(hz:t∈Icc (0:ℝ) 1)(w:E4):‖b (t,w)‖≤ |C|:= by by_cases hw:w∈K; exact le_trans (hC _ ⟨hz,hw⟩) (le_abs_self _); rw [hb t w hw,norm_zero]; exact abs_nonneg _
   have hy : (∫ v:E4,f 0 v)= b (0,x j) := by simp [f,integral_mul_const,source_profile.2]
   rw [← hy]
   refine Tendsto.congr' (mem_of_superset self_mem_nhdsWithin (fun t ht=> (hv t ht).symm)) ?_
   apply tendsto_integral_filter_of_dominated_convergence (fun v:E4=> ‖source 1 v‖ * |C|) _ _ (source_profile.1.norm.mul_const _)
   · refine Eventually.of_forall fun v => ?_
     exact (((show Continuous (fun t:ℝ=> f t v) from continuous_const.mul (he.comp (by fun_prop : Continuous (fun t:ℝ=> (t,x j+t • v))))).continuousAt).continuousWithinAt)
   · refine Eventually.of_forall fun t=>?_
     exact ((source_diff (show (0:ℝ)<1 from one_pos)).continuous.mul (he.comp (f:=fun v:E4=> (t,x j+t • v)) (by fun_prop))).aestronglyMeasurable
   filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (show (0:ℝ)<1 from one_pos))] with t hz hp
   exact Eventually.of_forall fun v=> le_trans (norm_mul_le ..) (mul_le_mul_of_nonneg_left (ht t ⟨le_of_lt hz,le_of_lt hp⟩ _) (norm_nonneg _))
end edge

include h
theorem pierce (hl:∀ i,(l i).loc=i) : spark_at l j (l j).dual m x R ρ =
    (if (l j).i=m then 2⁻¹ else 0:ℂ)* (↑(bypass x l j 0 (x j)):ℂ) := by
   let χ := flag x R j
   let f:= shot (x:=x) l j (l j).dual m
   let c:ℝ:= if (l j).i=m then 2⁻¹ else 0
   have hk : ((if (l j).i=m then 2⁻¹ else 0:ℂ):ℂ)= ↑c:= by unfold c; split <;> simp
   rw [hk,← ofReal_mul]
   apply tendsto_nhds_unique (shotLimit h l (j:=j) hl _ _ -- args
    ) ((continuous_ofReal.continuousAt (x:=c*_)|>.tendsto).comp (show Tendsto (fun t=>∫ w,f t w) _ _ from ?_))
   let b(p:ℝ × E4):= piece x l j χ p.1 p.2
   have hc:= h.flag_cost j; have hg:= h.flag_uniq j
   have he : Continuous b:= (piece_smooth x l j (χ:=χ) (flag_smooth (x:=x) (R:=R) j) (fun i hi=> h.flags j hi)).continuous
   have hz: b (0,x j)=bypass x l j 0 (x j):= by unfold b piece; rw [show χ (x j)=1 from hg.eq_of_nhds,one_mul]
   rw [←hz]
   have hy : (∫ v:E4,(1-χ v)*f 0 v)+c*b (0,x j)=c*b (0,x j):= by
      suffices heq: (∫ v:E4,(1-χ v)*f 0 v)=0 by rw [heq,zero_add]
      apply integral_eq_zero_of_ae
      filter_upwards [volume.ae_ne (x j)] with w hw
      change _ * (clasp _ _ _ _ _ _ * _)=0
      rw [minus_zero _ _ _ (sub_ne_zero.mpr hw), zero_mul,mul_zero]
   rw [← hy]; apply shot_follows h l j (l j).dual m (flag_smooth ..|>.continuous) hc hg
   have hh:= absorbing (x:=x) j b he hc (fun t v hv=>by
      unfold b piece; rw [show χ v=0 from image_eq_zero_of_notMem_tsupport hv,zero_mul])
   apply (hh.const_mul c).congr'; filter_upwards [self_mem_nhdsWithin] with t ht
   rw [← integral_const_mul]; apply integral_congr_ae; refine Eventually.of_forall fun v=>?_
   change _= χ v*(clasp _ _ _ _ _ _ * _)
   have hk : 0<t:=ht
   rw [same _ _ _ (by simp [hk.ne'])]; unfold b piece c; push_cast; split_ifs <;> ring

end YM.SchemeConversionRG11.FirstMS.Triad
