import YM.SchemeConversionRG11.FirstMS.Triad.Counter

/-! Value-subtracted mixed kernel. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MeasureTheory Metric Complex DR Maxwell Maxwell.Free Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable (x:Nodes) (l:P→Stem)(i:Fin 3)

lemma clasp_expense (h:Bool)(v:Bool)(i j:Fin 3):∃ L>0, ∀ t:ℝ,∀ w:E4, w≠0→‖clasp h i v j t w‖≤ L / ‖w‖^4:= by
   choose C hC hc using surf_prices h i
   let a:=∑ a:Axis,∑ b:Axis,‖fan v j a b‖ * C a b
   have ha:0≤a:=Finset.sum_nonneg fun i _=> Finset.sum_nonneg fun j _=>mul_nonneg (norm_nonneg _) (hC i j).le
   refine ⟨1+a,by positivity,fun t w hw=>?_⟩
   apply le_trans _ (show a/‖w‖^4 ≤ _ by gcongr; simp)
   unfold clasp a; simp_rw [Finset.sum_div]; apply (norm_sum_le ..).trans
   refine Finset.sum_le_sum fun i _=>le_trans (norm_sum_le ..) (Finset.sum_le_sum fun b _=>?_)
   exact (norm_mul_le ..).trans ((mul_le_mul_of_nonneg_left (hc _ _ _ _ hw) (norm_nonneg _)).trans_eq ((mul_div_assoc ..).symm))

local notation "z" => x 0
local notation "A" => x (1:Fin 3)
local notation "Yv" => x (2:Fin 3)
local notation "B" => bypass x l 0
local notation "K" => zone z A Yv
local notation "T" => shot (x:=x) l 0 false i

def tread (v:E4):ℝ:= mixed (l 0).i i (z-v)*(B 0 v-B 0 z)
def frolic (v:E4):ℝ:= mixed (l 0).i i (z-v)*B 0 v

variable (hc:x∈conf 3)(hl: (l 0).dual=true)
include hc
lemma tidy (w:E4)(hw:w∈ K)(t:ℝ): ContDiffAt ℝ ∞ (uncurry B) (t,w):= by
   obtain ⟨h₁,h₂⟩:=zone_separated (x:=A) (y:=Yv) (hc.ne (by decide : (0:Fin 3)≠1)) (hc.ne (by decide : (0:Fin 3)≠2)) hw
   apply bypass_smooth; intro i hj; fin_cases i
   · exact False.elim (hj rfl)
   · exact Or.inr h₁
   exact Or.inr h₂
include hl
lemma inside_zero :
   IntegrableOn (tread x l i) K ∧ Tendsto (fun t=>∫ w in K, T t w) (𝓝[>] 0) (𝓝 (∫ w in K, tread x l i w)):= by
   let f(t:ℝ)(w:E4):=clasp true (l 0).i false i t (w-z)*(B t w-B t z)
   let L:= volume.restrict K; have hm : MeasurableSet K:= isClosed_closedBall.measurableSet; have ht : IsCompact K:= isCompact_closedBall ..
   let F(p:ℝ × E4):= fderiv ℝ (B p.1) p.2
   have he(t:ℝ)(v:E4)(hv:v∈ K): ContinuousAt F (t,v):= (ContDiffAt.fderiv (g:=Prod.snd) (f:=fun p:ℝ × E4=>B p.1) ((tidy x l hc v hv t).comp (f:=fun p:(ℝ × E4)×E4=>(p.1.1,p.2)) ((t,v),v) (by fun_prop)) contDiffAt_snd (by simp : (∞:WithTop ℕ∞)+1≤∞)).continuousAt
   obtain ⟨P,hP⟩:= (isCompact_Icc.prod ht).exists_bound_of_continuousOn (f:=F) (s:= Icc (0:ℝ) 1 ×ˢ K) (fun p hp=> he p.1 p.2 hp.2 |>.continuousWithinAt)
   have hLip(t)(hz:t∈Icc (0:ℝ) 1)(v:E4)(hv:v∈K) : ‖B t v-B t z‖ ≤ P*‖v-z‖:=
      Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (fun w hw=> ((tidy x l hc w hw t).comp (f:=fun v:E4=>(t,v)) w (by fun_prop)).differentiableAt (by simp)) (fun w hw=> hP (t,w) ⟨hz,hw⟩) (convex_closedBall ..) (zone_self ..) hv
   obtain ⟨D,hD,hd⟩:= clasp_expense true false (l 0).i i
   have h(t)(hz:t∈Icc (0:ℝ) 1) : ∀ᵐ v∂L,‖f t v‖ ≤ D*|P| *branch v z:= by
      filter_upwards [ae_restrict_mem hm,ae_restrict_of_ae (volume.ae_ne z)] with v hv hy
      have hx:=norm_pos_iff.mpr (sub_ne_zero.mpr hy)
      refine (norm_mul_le ..).trans ((mul_le_mul (hd t _ (sub_ne_zero.mpr hy)) (hLip t hz v hv) (norm_nonneg _) (by positivity)).trans ?_)
      unfold branch; grw [le_abs_self P]; field_simp; rfl
   have hw(t:ℝ): AEStronglyMeasurable (f t) L:= by
      have he : Measurable (fun w:E4=>B t w):= Finset.measurable_prod _ (fun i (_:i∈_)=> (measurable_of_continuousOn_compl_singleton (x i) (f:=leg x l t i) (fun v hv=> ((leg_smooth x l i (v:=v) (t:=t) (Or.inr hv)|>.continuousAt).comp (f:=fun v:E4=>(t,v)) (by fun_prop)).continuousWithinAt)))
      have hh (a b:Axis): Measurable (fun v:E4=>surf true (l 0).i a b t (v-z)):=
        (measurable_of_continuousOn_compl_singleton (a:=(0:E4)) (f:=surf true (l 0).i a b t) (fun v hv=> ((surf_ok _ _ _ _ (p:=(t,v)) (show (t,v)≠_ from fun he=>hv (by simp [show v=0 from congrArg Prod.snd he]))|>.continuousAt).comp (f:=fun v:E4=>(t,v)) (by fun_prop)).continuousWithinAt)).comp (measurable_id.sub_const _)
      exact ((Finset.measurable_sum _ fun a (_:a∈Finset.univ)=>Finset.measurable_sum _ fun b (_:b∈Finset.univ)=> (hh a b).const_mul (fan false i a b)).mul ((he.sub_const _))).aestronglyMeasurable
   have hQ : Integrable (fun v=> D*|P| *branch v z) L := (one_tree z|>.integrableOn_isCompact ht).const_mul _
   have hv : tread x l i =ᵐ[L] f 0:= by
      filter_upwards [ae_restrict_of_ae (volume.ae_ne z)] with v hv; unfold f tread; rw [mixed_value _ _ (sub_ne_zero.mpr hv),show z-v=-(v-z) by abel,mixed_negative _ _ (sub_ne_zero.mpr hv)]
   refine ⟨(integrable_congr hv).2 (hQ.mono' (hw 0) (h 0 ⟨by rfl,by norm_num⟩)),?_⟩
   have hg : Tendsto (fun t=>∫ v in K,f t v) (𝓝[>] 0) (𝓝 (∫ v in K,f 0 v)) := by
      apply tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall hw) _ hQ
      · filter_upwards [ae_restrict_mem hm,ae_restrict_of_ae (volume.ae_ne z)] with v hv hy
        have he : ContinuousAt (fun t=> f t v) 0:=
          ContinuousAt.mul (f:=fun t=>clasp true (l 0).i false i t (v-z)) (by
             unfold clasp
             apply tendsto_finsetSum; intro a ha; apply tendsto_finsetSum; intro b hb
             have hr : v-z≠0:=sub_ne_zero.mpr hy
             exact (((surf_ok true (l 0).i a b (p:=((0:ℝ),v-z)) (by simp [hr])|>.continuousAt).comp (f:=fun t:ℝ=>(t,v-z)) (by fun_prop)).const_mul _)
            ) ((((tidy x l hc v hv 0).continuousAt).comp (f:=fun t:ℝ=>(t,v)) (by fun_prop)).sub (((tidy x l hc z (zone_self ..) 0).continuousAt).comp (f:=fun t:ℝ=> (t,z)) (by fun_prop)))
        exact he.continuousWithinAt
      filter_upwards [self_mem_nhdsWithin,eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (show (0:ℝ)<1 from one_pos))] with t ht hk; exact h _ ⟨(show 0<t from ht).le, hk.le⟩
   change Tendsto _ _ (𝓝 (∫ v,tread x l i v ∂L))
   rw [integral_congr_ae hv]; apply hg.congr'; filter_upwards [self_mem_nhdsWithin] with t hv
   have hC:=clasp_smooth (l 0).i i hv true false |>.continuous.comp (f:=fun w:E4=>w-z) (by fun_prop)
   have he : Continuous (B t):= continuous_iff_continuousAt.mpr fun w=> (bypass_smooth x l 0 (v:=w) (t:=t) (fun i _=>Or.inl (ne_of_gt hv))|>.continuousAt).comp (f:=fun v:E4=> (t,v)) (by fun_prop)
   unfold f shot; rw [hl]; simp_rw [mul_sub]; rw [integral_sub (f:=fun v:E4=> clasp true (l 0).i false i t (v-z)*B t v) (g:=fun v:E4=>clasp true (l 0).i false i t (v-z)*B t z) (hC.continuousOn.mul he.continuousOn |>.integrableOn_compact ht) ((hC.mul_const _).continuousOn.integrableOn_compact ht),integral_mul_const,show (∫ w in K,clasp true (l 0).i false i t (w-z))=0 from clear_zero _ _ hv _ z]; simp
lemma outside_zero {R ρ:ℝ}(h:Box x R ρ):
   IntegrableOn (frolic x l i) Kᶜ ∧ Tendsto (fun t=>∫ w in Kᶜ,T t w) (𝓝[>] 0) (𝓝 (∫ w in Kᶜ,frolic x l i w)):=by
   obtain ⟨D,hD,hd⟩:= clasp_expense true false (l 0).i i
   obtain ⟨Q,hQ,H⟩:= bypass_money x l 0 hc
   let r:=pairHole z A Yv
   have hr:0<r:=half_pos (lt_min (norm_pos_iff.mpr (sub_ne_zero.mpr (hc.ne (by decide : (0:Fin 3)≠1)))) (norm_pos_iff.mpr (sub_ne_zero.mpr (hc.ne (by decide : (0:Fin 3)≠2)))))
   let L:= volume.restrict Kᶜ; have hm : MeasurableSet Kᶜ:=isClosed_closedBall.measurableSet.compl
   have hb: Integrable (fun v=> D/r^4 * Q v) L:= (hQ.const_mul _).restrict
   have hh(t:ℝ) : ∀ᵐ v∂L, ‖T t v‖ ≤ D/r^4 * Q v:=by
      filter_upwards [ae_restrict_mem hm, ae_restrict_of_ae (H t)] with v hv hy
      have hp:r<‖v-z‖:= lt_of_not_ge fun he=>hv (mem_closedBall_iff_norm.mpr he)
      unfold shot; rw [hl]; exact (norm_mul_le ..).trans (mul_le_mul (le_trans (hd t _ (norm_pos_iff.mp (hr.trans hp))) (by gcongr)) hy (norm_nonneg _) (by positivity))
   have he: frolic x l i =ᵐ[L] T 0:= by
      filter_upwards [ae_restrict_of_ae (volume.ae_ne z)] with v hv
      unfold frolic shot; rw [hl,mixed_value _ _ (sub_ne_zero.mpr hv), show z-v=-(v-z) by abel,mixed_negative _ _ (sub_ne_zero.mpr hv)]
   have hy : ∀ᵐ v∂L,Tendsto (fun t=> T t v) (𝓝[>] 0) (𝓝 (T 0 v)):=by
      filter_upwards [ae_restrict_of_ae ((eventually_all_finset Finset.univ).2 (fun i _=>volume.ae_ne (x i)))] with v hv
      simp_rw [shot,live_signal]; apply tendsto_finsetSum; intro a ha; apply tendsto_finsetSum; intro b hh
      let u:= incline 0 l b
      have hq: ContinuousAt (fun t:ℝ=> softsphere x u 0 a t v) 0:= ((surface_smooth x u 0 a (t:=0) (v:=v) (Or.inr (hv 0 (Finset.mem_univ 0)))|>.continuousAt).mul (bypass_smooth x u 0 (t:=0) (v:=v) (fun i _=> Or.inr (hv i (Finset.mem_univ _)))|>.continuousAt)).comp (f:=fun t:ℝ=>(t,v)) (by fun_prop)
      exact (hq.const_mul _).continuousWithinAt
   have hT : ∀ᶠ t in 𝓝[>] 0, AEStronglyMeasurable (T t) L:= by filter_upwards [self_mem_nhdsWithin] with t ht; exact (shot_pays h l 0 false i ht).aestronglyMeasurable.restrict
   have hp : Integrable (T 0) L:= hb.mono' (by
      classical
      let f (t:ℝ):E4→ℝ:= if 0<t then T t else 0
      refine aestronglyMeasurable_of_tendsto_ae (𝓝[>] 0) (f:=f) (fun t=> ?_) ?_
      · unfold f; split_ifs with hz
        · exact (shot_pays h l 0 false i hz).aestronglyMeasurable.restrict
        exact aestronglyMeasurable_const
      exact hy.mono fun v hv=> hv.congr' (mem_of_superset self_mem_nhdsWithin (fun t ht=> show T t v=f t v from (by unfold f; rw [if_pos (show 0<t from ht)])))) (hh 0)
   refine ⟨(integrable_congr he).mpr hp,?_⟩; rw [integral_congr_ae (μ:=volume.restrict Kᶜ) he]
   exact tendsto_integral_filter_of_dominated_convergence _ hT (Eventually.of_forall hh) hb hy

theorem opponent {R ρ:ℝ}(h:Box x R ρ)(he:∀ i,(l i).loc=i): spark_at l 0 false i x R ρ=
    ((↑((∫ v in K,tread x l i v)+(∫ v in Kᶜ,frolic x l i v))):ℂ) := by
    apply tendsto_nhds_unique (shotLimit h l he _ false i) (continuous_ofReal.continuousAt|>.tendsto.comp ?_) -- inference
    apply ((inside_zero x l i hc hl).2.add (outside_zero x l i hc hl h).2).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact integral_add_compl (isClosed_closedBall.measurableSet) (shot_pays h l _ _ i ht)
end YM.SchemeConversionRG11.FirstMS.Triad
