import YM.SchemeConversionRG11.FirstMS.Triad.Coin

/-! Cut/paste integral toolkit for the three stems.
`V` and other finite indices all Fin 3 (canonical order).
Test Mollif moves p^t vary. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MSbar MeasureTheory Metric Complex DR Maxwell Maxwell.Free Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

variable (x:Nodes)(l:P→Stem)(j:P)(a:Axis)
-- distinct canonical order; at this point even if l isn't we define canon using x always

def leg (t:ℝ)(i:P)(v:E4) := soff (l i).dual (l i).i (l i).axis t (v-x i)
def surface (t:ℝ)(v:E4):= surf (l j).dual (l j).i a (l j).axis t (v-x j)
def bypass (t:ℝ)(v:E4):= ∏ i∈Finset.univ.erase j, leg x l t i v

def softsphere (t:ℝ)(v:E4):= surface x l j a t v * bypass x l j t v

lemma leg_smooth (i:P){t:ℝ}{v:E4} (hp : t≠0 ∨ v≠x i): ContDiffAt ℝ ∞ (fun p:ℝ × E4=> leg x l p.1 i p.2) (t,v):= by
   refine (soff_ok (l i).dual _ _ (p:=(t,v-x i)) ?_).comp (f:=fun p:ℝ × E4=>(p.1,p.2-x i)) (t,v) (by fun_prop)
   rintro hh; have he:=congr_arg Prod.fst hh; have hv:= congr_arg Prod.snd hh; exact hp.elim (· he) (· (sub_eq_zero.mp hv))
lemma surface_smooth {t:ℝ}{v:E4}(hp:t≠0∨v≠x j): ContDiffAt ℝ ∞ (uncurry (surface x l j a)) (t,v):= by
   refine (surf_ok (l j).dual _ _ _ (p:=(t,v-x j)) ?_).comp (f:=fun p:ℝ × E4=> (p.1,p.2-x j)) (t,v) (by fun_prop)
   rintro hh; exact hp.elim (· (congr_arg Prod.fst hh)) (· (sub_eq_zero.mp (congr_arg Prod.snd hh)))
lemma bypass_smooth {t:ℝ}{v:E4}(hp : ∀ i,i≠j→ t≠0 ∨ v≠x i): ContDiffAt ℝ ∞ (uncurry (bypass x l j)) (t,v):= by
   unfold uncurry bypass
   refine contDiffAt_prod (f:=fun i:P=>fun p:ℝ × E4=> leg x l p.1 i p.2) (t:=Finset.univ.erase j) (fun i hi=> leg_smooth x l i (hp _ (Finset.ne_of_mem_erase hi)))
lemma all_smooth {t:ℝ}(ht:0<t): ContDiff ℝ ∞ (softsphere x l j a t):= by
   have hh (v:E4) := ((surface_smooth x l j a (v:=v) (Or.inl ht.ne')).mul (bypass_smooth x l j (v:=v) fun _ _=> Or.inl ht.ne')).comp (f:=fun x:E4=> (t,x)) v (by fun_prop) -- t arg
   exact contDiff_iff_contDiffAt.mpr hh

lemma bypass_money (hc:x∈conf 3): ∃ Q:E4→ℝ, Integrable Q ∧ ∀ t:ℝ,∀ᵐ v:E4,‖bypass x l j t v‖≤Q v:=by
   have hp : (Finset.univ.erase j).card=2:= by rw [Finset.card_erase_of_mem (Finset.mem_univ j)]; simp [P]
   obtain ⟨b,c,hb,he⟩:= Finset.card_eq_two.mp hp
   obtain ⟨L,hL,hl⟩:= soff_prices (l b).dual (l b).i (l b).axis
   obtain ⟨D,hD,hd⟩:= soff_prices (l c).dual (l c).i (l c).axis
   refine ⟨_,(two_tree (hc.ne hb)).const_mul (L*D),fun t=>?_⟩
   filter_upwards [volume.ae_ne (x b),volume.ae_ne (x c)] with v vb vc
   rw [bypass,he,Finset.prod_pair hb]
   apply le_trans (norm_mul_le ..) (le_trans (mul_le_mul (hl t _ (sub_ne_zero.mpr vb)) (hd t _ (sub_ne_zero.mpr vc)) (norm_nonneg _) (by positivity)) _)
   unfold branch; rw [div_mul_div_comm,div_mul_div_comm]; simp [div_eq_mul_inv,mul_assoc]

lemma leg_local (i:P): ∃ Q:E4→ℝ, LocallyIntegrable Q ∧ ∀ t:ℝ,∀ᵐ v:E4, ‖leg x l t i v‖≤Q v:= by
   obtain ⟨L,hL,hl⟩:= soff_prices (l i).dual (l i).i (l i).axis
   refine ⟨fun v=> L*branch v (x i),?_,fun t=>?_⟩
   · intro z; obtain ⟨s,hs,h⟩:= one_tree (x i) z; exact ⟨s,hs,(show Integrable _ _ from h).const_mul L⟩
   exact (volume.ae_ne (x i)).mono (fun v hv=> le_trans (hl t _ (sub_ne_zero.mpr hv)) (by simp [branch,div_eq_mul_inv]))

lemma stem_earnest (hc:x∈conf 3){t:ℝ}(ht:0<t) : Integrable (fun v:E4=> leg x l t j v*bypass x l j t v):= by
   obtain ⟨Q,hQ,H⟩:= bypass_money x l j hc
   let f(v:E4):= leg x l t j v
   have hm : Continuous f := continuous_iff_continuousAt.mpr fun v=> (leg_smooth x l j (v:=v) (t:=t) (Or.inl ht.ne') |>.continuousAt).comp (f:=fun x:E4=> (t,x)) (by fun_prop)
   obtain ⟨C,h⟩ := (isCompact_closedBall (x j) 1).exists_bound_of_continuousOn hm.continuousOn -- actual pair
   obtain ⟨B,hB,h'⟩:= soff_prices (l j).dual (l j).i (l j).axis
   have hb(v:E4): ‖f v‖ ≤ max B C:= by
      by_cases he:v∈closedBall (x j) 1; exact le_trans (h v he) (le_max_right ..)
      have hu : 1<‖v-x j‖:=lt_of_not_ge (fun hv=> he (mem_closedBall_iff_norm.mpr hv)); apply le_trans (h' t _ (norm_pos_iff.mp (by linarith : 0< ‖v-x j‖))) _; exact (div_le_self hB.le (one_le_pow₀ hu.le)).trans (le_max_left ..)
   refine Integrable.mono' (hQ.const_mul (max B C)) (hm.mul (continuous_iff_continuousAt.mpr fun v => (bypass_smooth x l j (v:=v) (t:=t) (fun _ _=> Or.inl ht.ne')|>.continuousAt).comp (f:=fun x:E4=> (t,x)) (by fun_prop))|>.aestronglyMeasurable) ?_
   filter_upwards [H t] with v hv; exact le_trans (norm_mul_le ..) (mul_le_mul (hb v) hv (norm_nonneg _) (hB.le.trans (le_max_left ..)))

lemma exterior {χ:E4→ℝ} (hg:Continuous χ) (hm:HasCompactSupport χ) (hy:χ =ᶠ[𝓝 (x j)] fun _=>1) (hh:x∈conf 3):
   let F(t:ℝ)(v:E4) := (1-χ v)*softsphere x l j a t v
   (∀ t,Integrable (F t)) ∧ Tendsto (fun t=>∫ v,F t v) (𝓝[>] 0) (𝓝 (∫ v,F 0 v)):= by
   intro f
   obtain ⟨Q,hQ,H⟩:=bypass_money x l j hh
   obtain ⟨C,hC⟩:= hg.bounded_above_of_compact_support hm
   obtain ⟨L,hL,hl⟩:= surf_prices (l j).dual (l j).i a (l j).axis
   obtain ⟨r,hr,h⟩:= Metric.mem_nhds_iff.mp hy
   let B:= (1+|C|)* (L / r^4)
   have hp:0≤ B:= by unfold B; positivity
   have hw(t v): ‖(1-χ v)*surface x l j a t v‖ ≤ B:=by
      by_cases he:v∈ ball (x j) r
      · rw [show χ v = 1 from h he]; simpa using hp
      have hs:r ≤ ‖v-x j‖ := le_of_not_gt (fun hb=> he (mem_ball_iff_norm.mpr hb))
      apply (norm_mul_le ..).trans (mul_le_mul _ ((hl t _ (norm_pos_iff.mp (hr.trans_le hs))).trans _) (norm_nonneg _) (show 0≤1+|C| by positivity))
      · apply (norm_sub_le ..).trans; rw [norm_one]; grw [hC v, le_abs_self C]
      gcongr
   have hB:=hQ.const_mul B
   have hbc(t): ∀ᵐ v, ‖f t v‖≤ B*Q v:= by
      filter_upwards [H t] with v hv
      unfold f softsphere; rw [← mul_assoc]
      exact le_trans (norm_mul_le ..) (mul_le_mul (hw t v) hv (norm_nonneg _) hp)
   have hf(t): AEStronglyMeasurable (f t) volume:= by
      have hv(i:P): Measurable fun v:E4=> leg x l t i v:=
         measurable_of_continuousOn_compl_singleton (x i) fun v hv=> ((leg_smooth x l i (v:=v) (t:=t) (Or.inr hv)|>.continuousAt).comp (f:=fun x:E4=> (t,x)) (by fun_prop)).continuousWithinAt
      have hz : Measurable (surface x l j a t):= measurable_of_continuousOn_compl_singleton (x j) fun v hv=> ((surface_smooth x l j a (v:=v) (t:=t) (Or.inr hv)|>.continuousAt).comp (f:=fun x:E4=> (t,x)) (by fun_prop)).continuousWithinAt
      exact ((measurable_const.sub hg.measurable).mul (hz.mul (Finset.measurable_prod _ fun i _=> hv i))).aestronglyMeasurable
   refine ⟨fun t=>hB.mono' (hf t) (hbc t), tendsto_integral_filter_of_dominated_convergence (fun v=>B*Q v) (Eventually.of_forall hf) (Eventually.of_forall hbc) hB ?_⟩
   filter_upwards [eventually_all_finset Finset.univ|>.mpr (fun i _=> volume.ae_ne (x i))] with v hv
   have he: ContinuousAt (fun t => f t v) 0:= continuousAt_const.mul (((surface_smooth x l j a (v:=v) (t:=0) (Or.inr (hv j (Finset.mem_univ _)))|>.continuousAt).mul (bypass_smooth x l j (v:=v) (t:=0) (fun i _=> Or.inr (hv i (Finset.mem_univ _))) |>.continuousAt)).comp (f:=fun t:ℝ=>(t,v)) (by fun_prop))
   exact he.continuousWithinAt

end YM.SchemeConversionRG11.FirstMS.Triad
