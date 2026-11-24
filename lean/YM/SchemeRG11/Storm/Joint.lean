import YM.SchemeRG11.Storm.Resin
/-! Zone-dependent integration bills. -/
set_option autoImplicit false
set_option maxHeartbeats 240000
noncomputable section
namespace YM.SchemeRG11.Storm
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter TopologicalSpace Cluster Steam MSbar Pert Triangle
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace

-- handy radial overlap bound independent of directions

def wharf (z w : E4) := (‖w-z‖^3)⁻¹
lemma docks (z:E4) : LocallyIntegrable (wharf z) volume := by
  let f := wharf 0
  have hh (x:E4) : f x=(‖x‖^3)⁻¹ := by simp only [f,wharf,sub_zero]
  have hi : LocallyIntegrable f volume:= locallyIntegrable_of_norm_le_rpow (μ:=volume) (C:=1) (α:=(3:ℕ)) (by norm_num [Axis]) (by norm_num [Axis]) (Eventually.of_forall fun x=> by rw [hh,Real.norm_of_nonneg (by positivity : 0≤(‖x‖^3)⁻¹), Triangle.inv_power]; simp) (show Measurable f by unfold f wharf; fun_prop).aestronglyMeasurable
  let e:= Homeomorph.addRight (-z)
  rw [← show Measure.map e volume=(volume:Measure E4) from map_add_right_eq_self ..,locallyIntegrable_map_homeomorph] at hi
  convert! hi using 1; ext1 x; simp [Function.comp_apply,e,hh,wharf,sub_eq_add_neg]

private lemma refill {x y : E4} (hx : x≠y): ∃ K : Set E4,K ∈ 𝓝 x ∧ IsCompact K ∧ ContinuousOn (wharf y) K := by
  obtain ⟨K,hK,hx,h⟩:= exists_compact_subset isOpen_compl_singleton (show x∈({y}ᶜ:Set _) from hx)
  refine ⟨K,mem_interior_iff_mem_nhds.mp hx,hK,fun u hu=>?_⟩; have hh: u≠y:=h hu
  exact ((((continuousAt_id.sub continuousAt_const).norm.pow 3).inv₀ (show ‖u-y‖^3 ≠ 0 from pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hh)))).continuousWithinAt)
private lemma lands (z:E4) : ∀ᶠ w in cocompact E4, wharf z w ≤ 8/(1+‖w‖)^3 := by
  filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop (2+2*‖z‖))] with w hw
  have h:=norm_add_le (w-z) z; rw [sub_add_cancel] at h
  have he : (1+‖w‖)/2≤‖w-z‖:= by change 2+2*‖z‖≤‖w‖ at hw; linarith
  unfold wharf; grw [← he]; field_simp; norm_num
lemma docked {x y : E4} (hx : x≠y) : Integrable (wharf x * wharf y) volume := by
  have hp : LocallyIntegrable (wharf x * wharf y) volume := by
    intro z; by_cases h : z=x
    · subst z; obtain ⟨K,hK,hk,h⟩ := refill hx
      exact ⟨K,hK, ((docks x).integrableOn_isCompact hk).mul_continuousOn h hk⟩
    obtain ⟨K,hK,hk,h⟩:= refill h; exact ⟨K,hK,IntegrableOn.continuousOn_mul h ((docks y).integrableOn_isCompact hk) hk⟩
  refine integrable_iff_integrableAtFilter_cocompact.mpr ⟨?_,hp⟩
  let f:=fun w:E4=>64/(1+‖w‖)^6
  let s:= {w:E4 | ‖(wharf x * wharf y) w‖ ≤ f w}
  have hs : MeasurableSet s := measurableSet_le (show Measurable (fun w=> ‖(wharf x * wharf y) w‖) by unfold wharf; fun_prop) (by unfold f; fun_prop)
  refine ⟨s,?_,(pay_outer 64|>.integrableOn).mono' hp.aestronglyMeasurable.restrict (ae_restrict_of_forall_mem hs fun w hw=>hw)⟩
  refine ((lands x).and (lands y)).mono (fun w hw=>?_)
  change ‖wharf x w*wharf y w‖ ≤ _; rw [Real.norm_of_nonneg (by unfold wharf; positivity : 0≤wharf x w*wharf y w)]
  refine (mul_le_mul hw.1 hw.2 (by unfold wharf; positivity) (by positivity)).trans ?_
  unfold f; exact le_of_eq (by field_simp; norm_num)
end YM.SchemeRG11.Storm
