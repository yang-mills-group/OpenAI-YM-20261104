import YM.XSpace.Dyes
/-! # Elementary compact peak test -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory
open scoped Topology

-- avoids any disintegration/orbit null statement
lemma concentrating {V:Type*} [TopologicalSpace V][T2Space V][MeasurableSpace V][BorelSpace V]
    (μ: Measure V)[μ.IsOpenPosMeasure][IsFiniteMeasureOnCompacts μ]
    (K:Set V)(hK:IsCompact K){f g: V→ℝ}(hf:Continuous f)(hg: Continuous g)
    {D:ℝ}(hD:0<D)(h:∀ x∈K,g x∈ Icc 0 D)(he: ∀ x∈K,g x=D→0<f x)
    {x:V}(hx:x∈interior K)(hX:g x=D): ∀ᶠ n:ℕ in atTop,0 < ∫ y in K,f y*(g y)^n ∂μ := by
  let f₁ y:=max (f y) 0
  let f₂ y:=max (-f y) 0
  have h₁: Continuous f₁:= hf.max continuous_const; have h₂: Continuous f₂:= hf.neg.max continuous_const
  have hu₀ y : f y=f₁ y-f₂ y:= by
    unfold f₁ f₂; rcases le_total 0 (f y) with h|h; · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h),sub_zero]
    rw [max_eq_right h,max_eq_left (neg_nonneg.mpr h),zero_sub,neg_neg]
  let L:= K∩{x| f x≤0}
  have hl:L⊆ K:=inter_subset_left
  obtain ⟨B,hB,hB',HB⟩:∃ B:ℝ, 0≤B∧B<D ∧∀ x∈L,g x ≤ B := by
    by_cases hS:L.Nonempty
    · obtain ⟨s,hs,hp⟩:= (hK.inter_right (isClosed_le hf continuous_const)).exists_isMaxOn hS (hg.continuousOn.mono (inter_subset_left (t:={x|f x≤0})))
      exact ⟨g s,(h _ (hl hs)).1, lt_of_le_of_ne (h _ (hl hs)).2 (fun he'=> (he _ (hl hs) he').not_ge hs.2), fun z hz=>hp hz⟩
    exact ⟨0,le_refl _,hD,fun x hx=> (hS ⟨x,hx⟩).elim⟩
  obtain ⟨C,hC⟩:= hK.bddAbove_image h₂.continuousOn
  have hc :∀ y∈K, f₂ y≤ C:= fun y hy=>hC (mem_image_of_mem _ hy)
  let m:=(B+D)/2; have hm:B<m:=by unfold m; linarith
  have hm':m<D:=by unfold m; linarith
  have hs:0<f x:= he _ (interior_subset hx) hX
  let z:=f x/2
  have Hz:0<z:=half_pos hs
  let U:= interior K ∩ {y|m<g y}∩ {y| z < f₁ y}
  have ho: IsOpen U:=(isOpen_interior.inter (isOpen_lt continuous_const hg)).inter (isOpen_lt continuous_const h₁)
  have ht:x∈U:= ⟨⟨hx,show m<g x from hX.symm ▸ hm'⟩,(half_lt_self hs).trans_le (le_max_left ..)⟩
  have hUK:U⊆K:= fun _ h=> interior_subset h.1.1
  have ht':0<μ.real U:= ENNReal.toReal_pos (ho.measure_pos μ ⟨x,ht⟩).ne' ((measure_mono hUK).trans_lt hK.measure_lt_top).ne
  have hx: Tendsto (fun n:ℕ=> (B/m)^n) atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hB (hB.trans hm.le)) ((div_lt_one (lt_of_le_of_lt hB hm)).mpr hm)
  have hM: Tendsto (fun n:ℕ=> ((μ.real K)*C)*(B/m)^n) atTop (𝓝 0):= by simpa using hx.const_mul (μ.real K*C)
  filter_upwards [hM.eventually (gt_mem_nhds (show 0< (μ.real U)*z from mul_pos ht' Hz))] with n hp
  let F y:= f₁ y*g y^n; let Q y:= f₂ y*g y^n
  have hF: IntegrableOn F K μ:= (h₁.mul (hg.pow _)).continuousOn.integrableOn_compact hK
  have hQ: IntegrableOn Q K μ:= (h₂.mul (hg.pow _)).continuousOn.integrableOn_compact hK
  have ht y (hy:y∈K):0≤ F y:= mul_nonneg (le_max_right ..) (pow_nonneg (h y hy).1 _)
  have hu : μ.real U * (z*m^n) ≤ ∫ y in U,F y ∂μ := by
    rw [← show (∫ _ in U,z*m^n ∂μ)=μ.real U * (z*m^n) from setIntegral_const _]; apply setIntegral_mono_on (integrableOn_const ((measure_mono hUK).trans_lt hK.measure_lt_top).ne) (hF.mono_set hUK) ho.measurableSet; intro y hy; exact mul_le_mul_of_nonneg (hy.2.le) (pow_le_pow_left₀ (hB.trans hm.le) hy.1.2.le _) Hz.le (pow_nonneg (h y (hUK hy)).1 _)
  have hv := hu.trans (setIntegral_mono_set hF ((ae_restrict_mem hK.measurableSet).mono (fun y hy=> ht y hy)) ?_); rotate_left
  · exact hUK.eventuallyLE
  have hh : (∫ y in K,Q y ∂μ) ≤ μ.real K*(C*B^n):= by
    rw [← show (∫ _ in K,C*B^n ∂μ)=μ.real K * (C*B^n) from setIntegral_const _]; apply setIntegral_mono_on hQ (integrableOn_const hK.measure_lt_top.ne) hK.measurableSet; intro y hy
    by_cases hw:f y≤0
    · exact mul_le_mul_of_nonneg (hc y hy) (pow_le_pow_left₀ (h _ hy).1 (HB _ ⟨hy,hw⟩) _) (le_max_right ..) (pow_nonneg hB _)
    unfold Q f₂; rw [max_eq_right (by linarith),zero_mul]; exact mul_nonneg (le_trans (le_max_right _ _) (hc _ hy)) (pow_nonneg hB _)
  simp_rw [hu₀,sub_mul]; rw [integral_sub hF hQ, sub_pos]
  apply lt_of_le_of_lt hh ((show μ.real K*(C*B^n) < μ.real U*(z*m^n) from ?_).trans_le hv)
  have hm₀:=pow_pos (lt_of_le_of_lt hB hm) n
  change μ.real K*C*(B/m)^n<μ.real U*z at hp; rw [div_pow,← mul_div_assoc,div_lt_iff₀ hm₀,mul_assoc,mul_assoc] at hp; exact hp
end YM.XSpace.Stab
