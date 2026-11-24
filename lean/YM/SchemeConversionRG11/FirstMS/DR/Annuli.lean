import YM.SchemeConversionRG11.FirstMS.DR.Bump
import YM.Next.MAXWELL.Source

/-! A posteriori genuine Lorentz-dimensional position integration at 4D; no relying on the
value of integrals of non-L1 functions. Also useful for the compactified infinity tail. -/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.DR
open Function Set Filter MeasureTheory Metric
open scoped Topology ContDiff

section Lebesgue
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] 
variable {p : Type*} [MeasurableSpace p] {μ : Measure p} [SFinite μ]

/-- Shell change and swap from normalized-variable estimates. -/
theorem band {f g : p → E4 → E} {r : p → ℝ} {w : E4 → E} (x : E4)
   (hm : AEStronglyMeasurable (uncurry f) (μ.prod volume))
   (hn : ∀ᵐ t ∂μ, 0 < r t ∧ ∀ᵐ y ∂(volume:Measure E4), g t y = r t^4 • f t (x+r t • y))
   (he : Integrable (uncurry g) (μ.prod volume))
   (ht : ∀ᵐ y ∂(volume:Measure E4), w y = ∫ t, f t y ∂μ) :
   Integrable w ∧ (∫ y, w y) = ∫ t, (∫ y, g t y) ∂μ := by
  rcases (integrable_prod_iff he.aestronglyMeasurable).1 he with ⟨h₁,h₂⟩
  have h : Integrable (uncurry f) (μ.prod volume) := by
    refine (integrable_prod_iff hm).2 ⟨?_,?_⟩
    · filter_upwards [hn,h₁] with t ht hv; rcases ht with ⟨hr,ht⟩
      change Integrable (g t) at hv
      rw [integrable_congr ht] at hv
      have HH := (integrable_comp_smul_iff volume (fun y : E4 ↦ f t (x+y)) hr.ne').1 ((integrable_fun_smul_iff (pow_ne_zero 4 hr.ne') _).mp hv)
      change Integrable (f t)
      simpa using HH.comp_add_left (-x)
    apply h₂.congr
    filter_upwards [hn] with t ht; rcases ht with ⟨hr,ht⟩
    change (∫ y, ‖g t y‖) = ∫ y, ‖f t y‖
    rw [Maxwell.Free.dilate_integral (fun y=> ‖f t y‖) x (r t) hr, ← integral_smul]
    refine integral_congr_ae (ht.mono fun y hy=>?_)
    change ‖g t y‖=_
    rw [hy,norm_smul,Real.norm_of_nonneg (by positivity)]; rfl
  constructor
  · exact h.integral_prod_right.congr (ht.mono fun y hy=>hy.symm)
  rw [integral_congr_ae ht]
  change (∫ y, ∫ t, uncurry f (t,y) ∂μ) = _
  rw [← integral_prod_symm (uncurry f) h, integral_prod _ h]
  refine integral_congr_ae ?_
  filter_upwards [hn] with t hh; rcases hh with ⟨hr,ht⟩
  change (∫ y, f t y) = ∫ y, g t y
  rw [Maxwell.Free.dilate_integral (f t) x (r t) hr,← integral_smul,integral_congr_ae ht]

end Lebesgue

section Four
variable {F : E4 → ℂ} {R : ℝ} (hR : 0 < R) (x : E4)

include hR
variable {T : ℝ → E4 → ℂ}

/-- Analytic estimates on the scaled shell pay for the whole interior. -/
theorem near_part (hm : Measurable F)
   (hn : ∀ t ∈ Ioc 0 R, ∀ᵐ y ∂(volume:Measure E4), T t y = t^3 • ((lip (‖y‖^2)) • F (x+t • y))) -- parsing ^? lip ‖y‖ squared
   (he : Integrable (uncurry T) ((volume.restrict (Ioc 0 R)).prod volume)) :
    let p (y:E4) := cap (‖y-x‖^2/R^2) • F y
    Integrable p ∧ (∫ y, p y) = ∫ t in Ioc 0 R, ∫ y, T t y := by
    classical
    intro p
    let μ := volume.restrict (Ioc 0 R)
    let f (t:ℝ) (y:E4) := (lip (‖y-x‖^2/t^2)/t) • F y
    have hm' : Measurable (uncurry f) := by
      change Measurable fun z:ℝ×E4 => _ • F z.2
      exact (((lip_smooth.continuous.measurable).comp (f:=fun z:ℝ×E4 => ‖z.2-x‖^2/z.1^2)
          (((measurable_snd.sub_const _).norm.pow_const 2).div (measurable_fst.pow_const 2))).div measurable_fst).smul (hm.comp measurable_snd)
    apply band (μ:=μ) (r:=id) (w:=p) x hm'.aestronglyMeasurable _ he
    · filter_upwards [volume.ae_ne x] with y hy
      change cap _ • F y = ∫ t in Ioc 0 R, (lip (‖y-x‖^2/t^2)/t) • F y
      rw [integral_smul_const,scale_volume hR (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hy)) _)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hr : 0<t:=ht.1
    refine ⟨hr,(hn t ht).mono fun y hy=>?_⟩
    change T t y = t^4 • _
    dsimp only [f,id]
    rw [hy, add_sub_cancel_left, norm_smul,Real.norm_of_nonneg hr.le, mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hr.ne'), smul_smul,smul_smul]; congr 1
    field_simp

theorem outside_part (hm : Measurable F)
   (hn : ∀ t∈Ioc 0 R, ∀ᵐ y ∂(volume:Measure E4), T t y = (t⁻¹)^5 • (lip (‖y‖^2) • F (x+t⁻¹ • y)))
   (he : Integrable (uncurry T) ((volume.restrict (Ioc 0 R)).prod volume)) :
   let p (y:E4) := (1-cap (‖y-x‖^2*R^2)) • F y
   Integrable p ∧ (∫ y, p y) = ∫ t in Ioc 0 R, ∫ y, T t y := by
   intro p
   let μ:= volume.restrict (Ioc 0 R)
   let f(t:ℝ)(y:E4):= (lip (‖y-x‖^2*t^2)/t) • F y
   have hm' : Measurable (uncurry f):= by
      change Measurable fun z:ℝ×E4=>_ • F z.2
      exact (((lip_smooth.continuous.measurable).comp (f:=fun z:ℝ×E4=>‖z.2-x‖^2*z.1^2)
         (((measurable_snd.sub_const _).norm.pow_const 2).mul (measurable_fst.pow_const 2))).div measurable_fst).smul (hm.comp measurable_snd)
   apply band (μ:=μ) (r:=fun t=> t⁻¹) (w:=p) x hm'.aestronglyMeasurable _ he
   · filter_upwards with y
     change _ = ∫ t in Ioc 0 R, (lip (‖y-x‖^2*t^2)/t) • F y
     rw [integral_smul_const,dest_volume _ hR]
   filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
   have hr : 0<t := ht.1
   refine ⟨inv_pos.mpr hr,(hn t ht).mono fun y hy=>?_⟩
   dsimp only [f]
   rw [hy,add_sub_cancel_left,norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), mul_pow,show t⁻¹^2*‖y‖^2*t^2=‖y‖^2 by field_simp, smul_smul,smul_smul]; congr 1
   field_simp

end Four
end YM.SchemeConversionRG11.FirstMS.DR
