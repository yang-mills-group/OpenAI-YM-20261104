import YM.SchemeRG11.Bubble.Spine

/-! Bound on the surviving finite-part coefficient, fixed external domains. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.SchemeRG11.Bubble
open Function Set MeasureTheory Filter Metric Asymptotics Hot MSbar
open scoped ContDiff Topology
local notation "W" => ℝ×ℝ

lemma slim (A B : ℝ) (h : 1≤A+B) : (volume.real (foil A B)) ≤ A+B := by
  let s := Ioc (1:ℝ) (A+B) ×ˢ slab
  have hp : volume.real s = A+B-1 := by
    unfold Measure.real s slab; rw [show (volume : Measure W)=Measure.prod volume volume from rfl, Measure.prod_prod, ENNReal.toReal_mul]
    change Measure.real volume _*Measure.real volume _=_
    rw [Real.volume_real_Ioc,Real.volume_real_Ioc]; simp [h]
  apply le_trans (b:=volume.real s) (ENNReal.toReal_mono ?_ (measure_mono (foil_span A B))) (le_trans hp.le (by linarith))
  unfold s slab; rw [show (volume : Measure W)=Measure.prod volume volume from rfl,Measure.prod_prod]; simp
lemma lofty : (volume stem) < ⊤ := by
  rw [stem,show (volume : Measure W)= Measure.prod volume volume from rfl,Measure.prod_prod]; simp [slab]

variable {μ : ℝ} {w : ℝ→ℂ} (hw : Continuous w) {j : Bool} {P : ℂ→ℝ→ℂ} {D : ℂ→ℂ} {A B : ℝ}
include hw
theorem budget (C : ℝ) (hC : 0<C) (μ : ℝ) : ∃ L>0, ∀ (P : ℂ→ℝ→ℂ) (D : ℂ→ℂ) (A B : ℝ) (j : Bool), 1≤A+B →
    Ticket (P 0) (D 0) (A+B) C → ‖glide μ A B w P D j 0‖ ≤ L*(A+B) := by
  obtain ⟨H,hH,h⟩ := limit_w hw
  let Y := ‖Pole.factor μ 0‖
  let Z := ‖deriv (Pole.factor μ) 0‖
  let R:=‖route w‖*C; let S:=‖scale w‖*C
  let X:ℝ:=volume.real stem
  refine ⟨1+(Y*(H*C*X+H*C+R)+Z*(S+R)),by unfold Y X Z S R; positivity, fun P D A B j hh hs=>?_⟩
  have hP:=hs.body; have hD:=hs.star
  have hc : ‖P 0 0‖≤C:=hP 0 ⟨le_rfl,by linarith⟩
  have ha p (hp : p∈stem) : ‖purse w P D j 0 p‖ ≤ H*C := by
    simpa only [Complex.zero_re,Real.rpow_zero,mul_one] using estimate_small j hH h hC hs hp
  have h₁ := norm_setIntegral_le_of_norm_le_const lofty ha
  have hb := norm_setIntegral_le_of_norm_le_const (fpaid A B) (f:=pouch w P j 0) (C:=H*C) (fun p hp=> by
    simpa only [pow_zero,mul_one] using estimate_foil j hH h hC hs 0 (by norm_num : (0:ℂ).re-1 ≤ ((0:ℕ):ℝ)) hp)
  have h₂:=hb.trans (mul_le_mul_of_nonneg_left (slim A B hh) (by positivity))
  let a:= if j then (0-1:ℂ)⁻¹*route w*P 0 0 else 0; let b := if j then scale w*D 0 else route w*P 0 0
  have hN : 0≤R := mul_nonneg (norm_nonneg _) hC.le
  have hM : 0≤S := mul_nonneg (norm_nonneg _) hC.le
  have h₃ : ‖a‖≤R:=by cases j; simpa only [a,Bool.false_eq_true,↓reduceIte,norm_zero]; unfold a R; simp only [if_true, zero_sub,inv_neg,inv_one,norm_mul,norm_neg,norm_one,one_mul];gcongr
  have h₄ : ‖b‖≤S+R:=by
    cases j
    · unfold b; simp only [Bool.false_eq_true,↓reduceIte,norm_mul]; exact (mul_le_mul_of_nonneg_left hc (norm_nonneg _)).trans (by unfold R; linarith [hM])
    unfold b; simp only [if_true,norm_mul]; exact (mul_le_mul_of_nonneg_left hD (norm_nonneg _)).trans (by unfold S; linarith [hN])
  unfold glide restore; rw [dslope_same]
  refine (norm_add_le ..).trans ?_
  simp only [norm_mul]; change Y * ‖(∫ p in stem,_) + (∫ p in foil A B,_) + a‖ + Z*‖b‖ ≤ _
  have hY : 0≤Y:=norm_nonneg _; have hZ:0≤Z:=norm_nonneg _
  grw [norm_add_le,norm_add_le (∫ p in stem,_) (∫ p in foil A B,_),h₁,h₂,h₃,h₄]
  let K:=Y*(H*C*X+R)+Z*(S+R)
  calc _ = Y*(H*C)*(A+B)+K := by unfold K X; ring
       _ ≤ Y*(H*C)*(A+B)+K*(A+B) := add_le_add_right (by unfold K X; exact le_mul_of_one_le_right (by positivity) hh) _
       _ ≤ _ := by rw [← add_mul]; apply mul_le_mul_of_nonneg_right _ (by linarith); unfold K; linarith

theorem stabilizes {Y : Type} {v : Filter Y} [v.IsCountablyGenerated] (j : Bool) 
    {E : Y→ℂ→ℝ→ℂ} {F : Y→ℂ→ℂ} (h : ∀ᶠ y in v, Glaze (E y) (F y))
    {C : ℝ} (hC : 0<C) (he : ∀ᶠ y in v, Ticket (E y 0) (F y 0) (A+B) C)
    (ht : ∀ r≥(0:ℝ), Tendsto (fun y=>E y 0 r) v (𝓝 (P 0 r))) (hf : Tendsto (fun y=>F y 0) v (𝓝 (D 0))) :
    Tendsto (fun y=>glide μ A B w (E y) (F y) j 0) v (𝓝 (glide μ A B w P D j 0)) := by
  obtain ⟨H,hH,hW⟩:= limit_w hw
  have hx := ht _ (show 0≤(0:ℝ) from le_rfl)
  have h₁ := tendsto_integral_filter_of_dominated_convergence (μ:=volume.restrict stem) (fun _=> H*C) (F:=fun y=> purse w (E y) (F y) j 0) (l:=v) (f:=purse w P D j 0)
    (h.mono fun y hy=> (purse_on j hy hw 0).aestronglyMeasurable stem_meas)
    (he.mono fun y hy=> ae_restrict_of_forall_mem stem_meas (fun p hp=> by simpa using estimate_small j hH hW hC hy hp)) (integrableOn_const lofty.ne) (ae_restrict_of_forall_mem stem_meas (fun p hp=> by
      refine tendsto_const_nhds.mul ((ht _ (precis hp.2 hp.1.1).1).sub ?_)
      unfold localTerms
      split
      · exact hx.add (tendsto_const_nhds.mul hf)
      exact hx.add tendsto_const_nhds))
  have h₂ := tendsto_integral_filter_of_dominated_convergence (μ:=volume.restrict (foil A B)) (fun _=> H*C) (F:=fun y=> pouch w (E y) j 0) (l:=v) (f:=pouch w P j 0)
    (h.mono fun y hy=> (pouch_on j hy hw 0 A B).aestronglyMeasurable (foil_meas A B))
    (he.mono fun y hy=> ae_restrict_of_forall_mem (foil_meas ..) (fun p hp=> by simpa using estimate_foil j hH hW hC hy 0 (by norm_num : (0:ℂ).re-1 ≤ ((0:ℕ):ℝ)) hp)) (integrableOn_const (fpaid A B).ne) (ae_restrict_of_forall_mem (foil_meas ..) (fun p hp=>
       tendsto_const_nhds.mul (ht _ (precis hp.2.1 (lt_trans zero_lt_one hp.1)).1)))
  unfold glide
  refine (tendsto_const_nhds.mul ((h₁.add h₂).add ?_)).add (tendsto_const_nhds.mul ?_)
  · split
    · exact tendsto_const_nhds.mul hx
    exact tendsto_const_nhds
  split
  · exact tendsto_const_nhds.mul hf
  exact tendsto_const_nhds.mul hx
end YM.SchemeRG11.Bubble
