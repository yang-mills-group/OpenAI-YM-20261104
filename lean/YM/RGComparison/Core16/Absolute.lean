import YM.RGComparison.Core16.Grade

/-!
# Absolute moment bill for the complete normalized-history Taylor test

Also works in incidence of exceptional (power-flat) tags; no assuming smoothness of `|Y|`. This
is an auxiliary tool for paying real perturbations of the path parameters which may not be smooth.
Note that the bills here include the volume-dependent common dimensional extraction. Fixed torus.
-/
set_option autoImplicit false
noncomputable section

namespace YM.RGComparison.Core16.Descent
open Lattice RG Tree Wilson Precision Push.BetaTransport
open Function Filter MeasureTheory Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open PertExtension PertExtension.Series Tested Radial
variable {G : Gauge} {n c : Side} {d : Descent n c} (t : d.Tags)
    {f g : Fields G d → ℝ}

section calculus
variable {a : ℝ} {S : Set (Fields G d)}
lemma env_norm (hf : Envelope f) : Envelope fun x => ‖f x‖ := ⟨hf.meas.norm, by
  obtain ⟨C,hC⟩ := hf.cost
  exact ⟨C, fun i => by simpa using hC i⟩⟩
lemma env_realScale (hf : Envelope f) (a : ℝ) : Envelope (a • f) := (Envelope.const _).mul hf
lemma env_action (h : d.OK G) : Envelope (d.action (G := G) t 1) := by
  have H := account_envelope h 1 t
  obtain ⟨C,hC⟩ := H.cost
  exact ⟨H.meas.comp (measurable_const.prodMk measurable_id), C, fun x => hC (1,x)⟩
lemma env_field (d : Descent n c) (F : Config G n → ℝ) (h : Continuous F) : Envelope (F ∘ d.fine 1) := by
  have hf := (show Continuous (d.fine (1 : Config G c)) from
    (fine_continuous d).comp (continuous_const.prodMk continuous_id))
  have hs := h.comp hf
  have he := isCompact_univ.exists_bound_of_continuousOn hs.continuousOn
  exact ⟨hs.measurable, he.choose, fun x => he.choose_spec _ (mem_univ x)⟩

lemma monotonicity (h : d.OK G) (hf : Envelope f) (hg : Envelope g) (hP : f ≤ g)
    (ha : 0 < a) : region t f S a ≤ region t g S a := by
  unfold region
  apply mul_le_mul_of_nonneg_left _ (by positivity); apply integral_mono (pow_env t f h hf _|>.integrable (d.measure G)|>.integrableOn)
    (pow_env t g h hg _|>.integrable (d.measure G)|>.integrableOn)
  intro i; unfold power
  gcongr; exacts [probability_nonneg d .., hP i]

lemma region_nonneg (hf : 0 ≤ f) (ha : 0 < a) (S : Set (Fields G d)) : 0 ≤ region t f S a := by
  have he (i : Fields G d) := hf i
  unfold region; refine mul_nonneg (by positivity) (integral_nonneg fun i => ?_)
  exact mul_nonneg (mul_nonneg (probability_nonneg d ..) (he i)) (Real.exp_pos _).le

lemma region_add (h : d.OK G) (hf : Envelope f) (hg : Envelope g) (S : Set (Fields G d)) (a : ℝ) :
    region t (f+g) S a = region t f S a + region t g S a := by
  have hw i : power t (f+g) a i = power t f a i + power t g a i := by simp only [power, Pi.add_apply, mul_add, add_mul]
  unfold region; simp_rw [hw,← mul_add]
  rw [integral_add ((pow_env t f h hf a).integrable (d.measure G)|>.integrableOn)
    ((pow_env t g h hg a).integrable (d.measure G)|>.integrableOn)]

lemma region_scale (c a : ℝ) (f : Fields G d → ℝ) (S : Set (Fields G d)) :
    region t (c • f) S a = c * region t f S a := by
  have hh x : power t (c • f) a x=c * power t f a x := by unfold power;rw [Pi.smul_apply,smul_eq_mul]; ring
  unfold region; simp_rw [hh, integral_const_mul]; ring

lemma region_sub (h : d.OK G) (hf : Envelope f) (hg : Envelope g) (S : Set (Fields G d)) (a : ℝ) :
    region t (f-g) S a = region t f S a - region t g S a := by
  rw [show f-g=f+ (-1:ℝ) • g by simp [sub_eq_add_neg], region_add t h hf (env_realScale hg (-1)), region_scale]; ring

lemma region_le_abs (f : Fields G d → ℝ) (ha : 0 < a) (S : Set (Fields G d)) :
    ‖region t f S a‖ ≤ region t (fun x => ‖f x‖) S a := by
  unfold region; rw [norm_mul,Real.norm_of_nonneg
    (by positivity : 0 ≤ (a^Module.finrank ℝ (Coordinates G d))⁻¹)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have he (i) : power t (fun i => ‖f i‖) a i = ‖power t f a i‖ := by
    simp only [power, norm_mul,Real.norm_of_nonneg (probability_nonneg ..),Real.norm_of_nonneg (Real.exp_pos _).le]
  simp_rw [he]; exact norm_integral_le_integral_norm _
end calculus

section estimate
variable (P : ChartRatio G) (R : LocalRatio P) (h : d.Room G)
    {w : ℕ} (hv : d.SmoothAtFlat f) (hy : RadialOrder w (f ∘ d.tablePath)) (hs : Envelope f)
include R h hv hy hs

/-- Take the top field grade into the absolute integration budget BEFORE division by its couplings.
No estimate on the probability of individual flags after stopping hidden in this lemma. -/
theorem absolute_grade : Bill w (region t (fun i => ‖f i‖) univ) := by
  let f' (i : Fields G d) := ‖f i‖
  have he := expands P R t 1 h (Envelope.const _) contDiffAt_const
  have hy : d.SmoothAtFlat (f*f) := hv.mul hv
  -- pointwise trick: compare norm of field using energy budget on the smooth square of the field
  obtain ⟨C,hC,F⟩ := he.bounded
  obtain ⟨D,hD,K⟩ := region_grade P R h hy (fun x => bill_mul (‹RadialOrder w _› x) (‹RadialOrder w _› x)) t (hs.mul hs)
  refine ⟨C+D,by positivity,?_⟩
  filter_upwards [F,K,eventually_pos] with a hF hG ha
  let c := a^w; have hc : 0<c := by unfold c; positivity
  have hh (x : Fields G d) : c * f' x ≤ c*c + f x * f x := by
    change c*|f x| ≤ _; nlinarith only [sq_nonneg (c-|f x|),sq_abs (f x),hc]
  have hr := monotonicity t (S:=univ) (room_ok d h) (env_realScale (env_norm hs) c)
    ((env_realScale (Envelope.const 1) (c*c)).add (hs.mul hs)) (f:=c • f') (g:=(c*c) • 1 + f*f)
    (fun x => by simpa using hh x) ha
  rw [region_scale,region_add (f := (c*c) • 1) (g := f*f) t (room_ok d h) (env_realScale (Envelope.const 1) _) (hs.mul hs), region_scale] at hr
  rw [Real.norm_of_nonneg (region_nonneg (f:=f') t (fun _ => norm_nonneg _) ha univ)]
  apply le_of_mul_le_mul_left (a:=c) _ hc
  apply hr.trans; simp only [pow_zero,mul_one] at hF
  apply (add_le_add (b:=c*c*C) (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hF) (by positivity))
    ((le_abs_self _).trans hG)).trans_eq
  unfold c; rw [pow_add]; ring

end estimate
end YM.RGComparison.Core16.Descent
