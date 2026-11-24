import YM.SchemeConversionRG11.FirstMS.Triad.Soft
import YM.Pert.Triangle.Price

/-! Distance envelopes. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MSbar MeasureTheory Metric Complex DR Maxwell Maxwell.Free Pert.Triangle Analysis TopologicalSpace
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable (h:Bool)(i:Fin 3)(a μ:Axis)

private lemma smooth_radius {n:ℕ} (H : ℝ × E4→ℝ)
    (hF: ∀ x, x ≠ 0 → ContinuousAt H x)
    (h:∀ r:ℝ,0<r→∀ v : ℝ × E4,v≠0→ H v=r^n*H (r • v)): ∃ C>0,∀ t v,v≠(0:E4)→ ‖H (t,v)‖≤ C / ‖v‖^n:=by
   obtain ⟨C,hC⟩:= (isCompact_sphere (0:ℝ×E4) 1).exists_bound_of_continuousOn fun x hx=> ContinuousAt.continuousWithinAt (hF x (by rintro rfl; simp at hx))
   refine ⟨|C|+1,by positivity,fun t v hv=>?_⟩
   let z:ℝ × E4:= (t,v); have hp : z≠0:= fun h=>hv (congrArg Prod.snd h)
   have hr : 0<‖z‖:=norm_pos_iff.mpr hp
   have hs : ‖z‖⁻¹ • z∈sphere (0:ℝ×E4) 1:=by rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hr.ne']
   change ‖H z‖≤_
   rw [h _ (inv_pos.mpr hr) z hp, norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ ‖z‖⁻¹^n)]
   grw [hC _ hs, le_trans (le_abs_self C) (by linarith : |C| ≤ |C|+1)]
   rw [inv_pow, div_eq_mul_inv, mul_comm]; gcongr
   exact norm_snd_le z

lemma soff_prices : ∃ C>0, ∀ t v, v≠(0:E4)→ ‖soff h i μ t v‖ ≤ C/ ‖v‖^3 := by
   refine smooth_radius (uncurry (soff h i μ)) (fun _ hp=> (soff_ok h i μ hp|>.continuousAt)) ?_
   rintro r hr ⟨t,p⟩ hp
   have hv := refilling (t,p) hp
   have he : (r*t)^2+‖r • p‖^2=r^2*(t^2+‖p‖^2):=by rw [norm_smul, Real.norm_of_nonneg hr.le]; ring
   change soff _ _ _ t p=r^3*soff h i μ (r*t) (r • p)
   unfold soff; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _=>?_
   unfold sol; rw [soften_first (show (r*t)^2+‖r • p‖^2≠0 by rw [he]; exact (mul_pos (pow_pos hr _) hv).ne'),soften_first hv.ne',he,PiLp.smul_apply,smul_eq_mul]
   field_simp
lemma surf_prices : ∃ C>0, ∀ t v, v≠(0:E4)→ ‖surf h i a μ t v‖ ≤ C/ ‖v‖^4 := by
   refine smooth_radius (uncurry (surf h i a μ)) (fun _ hp=> (surf_ok h i a μ hp|>.continuousAt)) ?_
   rintro r hr ⟨t,p⟩ hp; have hv := refilling (t,p) hp
   have he : (r*t)^2+‖r • p‖^2=r^2*(t^2+‖p‖^2):=by rw [norm_smul, Real.norm_of_nonneg hr.le]; ring
   have hx: (r*t,r • p)≠0:= smul_ne_zero hr.ne' hp
   change surf h i a μ t p=r^4*surf h i a μ (r*t) (r • p)
   rw [surf_value _ _ _ _ hp,surf_value _ _ _ _ hx, Finset.mul_sum]; refine Finset.sum_congr rfl fun b _=>?_
   rw [soften_second (show (r*t)^2+‖r • p‖^2≠0 by rw [he];exact (mul_pos (pow_pos hr _) hv).ne'),soften_second hv.ne',he]
   simp only [PiLp.smul_apply,smul_eq_mul]; field_simp

-- product two M

def branch (p x : E4) := (1:ℝ)/‖p-x‖^3

lemma one_tree (x:E4): LocallyIntegrable (fun p:E4=> branch p x) := by
   let f:= fun p:E4=> (1:ℝ)/‖p‖^3
   have hi : LocallyIntegrable f:= locallyIntegrable_of_norm_le_rpow (α:=((3:ℕ):ℝ)) (μ:=volume) (C:=1) (by norm_num [four_rank]) (by norm_num [four_rank]) (Eventually.of_forall fun x:E4=> by
      rw [inv_power,one_mul]; simp [f]) (show Measurable f by unfold f; fun_prop).aestronglyMeasurable
   let e:=Homeomorph.addRight (-x);have : Measure.map e volume=(volume:Measure E4):=map_add_right_eq_self volume (-x)
   rw [←this,locallyIntegrable_map_homeomorph] at hi
   rw [show (fun w=>branch w x)= f ∘ e from funext fun w=> by simp [branch,f,e,sub_eq_add_neg]]
   exact hi
private lemma small (x y : E4) (h:y≠x): ∃ K∈𝓝 y, IsCompact K ∧ ContinuousOn (fun v=> branch v x) K := by
   obtain ⟨r,hr,H⟩:= Metric.mem_nhds_iff.mp (isOpen_compl_singleton.mem_nhds (show y∈{x}ᶜ from h)); refine ⟨closedBall y (r/2),closedBall_mem_nhds _ (half_pos hr),isCompact_closedBall ..,fun z hz=>?_⟩
   have hw:= H (closedBall_subset_ball (half_lt_self hr) hz); change z≠x at hw
   exact (continuousAt_const.div (((continuousAt_id.sub continuousAt_const).norm).pow 3) (pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw)))).continuousWithinAt

lemma two_tree {x y:E4}(hp:x≠y): Integrable (fun v=> branch v x*branch v y) := by
   have hk : LocallyIntegrable (fun v=> branch v x*branch v y):= by
      intro z; by_cases hz:z=x
      · subst z; obtain ⟨K,hK,hC,hF⟩:=small y x hp
        exact ⟨K,hK, IntegrableOn.mul_continuousOn ((one_tree x).integrableOn_isCompact hC) hF hC⟩
      obtain ⟨K,hK,hC,hF⟩:=small x z hz
      exact ⟨K,hK,IntegrableOn.continuousOn_mul hF ((one_tree y).integrableOn_isCompact hC) hC⟩
   have he(x:E4) : ∀ᶠ w in cocompact E4,‖branch w x‖≤ 8/(1+‖w‖)^3:= by
      filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop (2+2*‖x‖))] with w hw; change 2+2*‖x‖ ≤ ‖w‖ at hw
      have hb:= norm_sub_norm_le w x; have hq:(1+‖w‖)/2 ≤ ‖w-x‖:= by linarith
      have ha : 0<(1+‖w‖)/2:= by positivity
      unfold branch; rw [Real.norm_of_nonneg (by positivity)]; grw [←hq]; field_simp; linarith
   let K:={v:E4| ‖branch v x*branch v y‖ ≤64/(1+‖v‖)^6}
   have h : K∈cocompact E4 := mem_of_superset (inter_mem (he x) (he y)) (fun v (hv:_ ∧ _)=>by
      apply le_trans (norm_mul_le ..) (le_trans (mul_le_mul hv.1 hv.2 (norm_nonneg _) (by positivity)) _); field_simp; norm_num)
   rw [integrable_iff_integrableAtFilter_cocompact]; refine ⟨⟨K,h,(pay_outer 64|>.integrableOn (s:=K)).mono' hk.aestronglyMeasurable.restrict (ae_restrict_mem ?_)⟩,hk⟩
   exact measurableSet_le (f:=fun v=>‖branch v x*branch v y‖) (g:=fun v:E4=>64/(1+‖v‖)^6) (by unfold branch; fun_prop) (by fun_prop)

end YM.SchemeConversionRG11.FirstMS.Triad
