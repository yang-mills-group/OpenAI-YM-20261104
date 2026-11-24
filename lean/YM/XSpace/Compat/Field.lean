import YM.XSpace.Compat.Hill
import YM.Further.FREE_COVARIANCE_KP.KP.Field
import YM.Maxwell.PotentialKernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! Additive compatibility closure from pinned Oct15 ancestry.
Current baseline definitions are reused; extracted declaration text is unchanged.
Prepared for independent checking; no successful build is claimed here. -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Compat.KP
open YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory VectorFourier GaussianFourier
open scoped Topology ContDiff BigOperators InnerProductSpace FourierTransform Real

def water (p:E4) : ℂ := breeze 1 p * (spine p)⁻¹

lemma go_real {μ : Measure ℝ} (f:ℝ→ℝ) : ∫ x, (↑(f x):ℂ) ∂μ = ↑(∫ x, f x ∂μ) := integral_ofReal

private lemma song_breeze (t:ℝ) (x p:E4) : song x p*breeze t p = Complex.exp (-(t:ℂ)*↑‖p‖^2 + I*(⟪x,p⟫_ℝ:ℂ)) := by
  unfold song breeze polar; rw [london_at,ofReal_exp,← Complex.exp_add]; congr 1; push_cast; ring

private lemma gaussian (t:ℝ) (ht : 0<t) (x:E4) : ∫ p, song x p*breeze t p = ↑((π/t)^2 * Real.exp (-(‖x‖^2/4) /t)) := by
  simp_rw [song_breeze]
  rw [integral_cexp_neg_mul_sq_norm_add (show 0<(↑t:ℂ).re from ht)]
  simp only [E4,YM.Axis,finrank_euclideanSpace_fin,I_sq]
  norm_num [Complex.cpow_ofNat]
  left
  congr 1
  ring

private lemma gauss_sum (x:E4) : Integrable (fun y : ℝ×E4 => song x y.2*breeze y.1 y.2) ((volume.restrict (Ioi 1)).prod volume) := by
  let F := fun (t:ℝ) (p:E4) => Complex.exp (-(t:ℂ)*↑‖p‖^2 + I*(⟪x,p⟫_ℝ:ℂ))
  have hm : Continuous (uncurry F) := by unfold F uncurry; fun_prop
  refine (integrable_prod_iff (by simp_rw [song_breeze]; exact hm.aestronglyMeasurable)).2 ⟨?_,?_⟩
  · filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
    simp_rw [song_breeze]; exact integrable_cexp_neg_mul_sq_norm_add (show 0<(↑t:ℂ).re from zero_lt_one.trans ht) I x
  have hh : IntegrableOn (fun t : ℝ => π^2*t^(-((↑(2:ℕ)):ℝ))) (Ioi 1) := (((integrableOn_Ioi_rpow_iff one_pos).2 (by norm_num)).const_mul _)
  apply hh.congr; filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
  have ht' : 0<t := zero_lt_one.trans ht
  have g := congr_arg Complex.re (gaussian t ht' 0)
  have h (p:E4) : song 0 p=1 := by simp [song,london_at]
  simp_rw [h,one_mul] at g
  have hg : ∫ p:E4, polar t p=(π/t)^2 := by
    have he : ∫ p:E4,breeze t p=↑(∫ p:E4,polar t p) := integral_ofReal
    rw [he] at g
    simp only [ofReal_re] at g
    simpa using g
  have hx (p:E4) : ‖song x p*breeze t p‖=polar t p := by
    rw [norm_mul,song_fee,one_mul]
    change ‖(↑(polar t p):ℂ)‖=_
    simp [abs_of_pos (show 0<polar t p from Real.exp_pos _)]
  simp_rw [hx,hg]; rw [Real.rpow_neg ht'.le,Real.rpow_natCast, div_pow]; ring

private lemma stale (r:ℝ) (hr : 0<r) : ∫ t:ℝ in Ioi 1, ((π/t)^2 * Real.exp (-r / t)) = π^2 / r * (1-Real.exp (-r)) := by
  let f (x:ℝ) := π^2 / r * Real.exp (-r / x)
  let g (x:ℝ) := (π / x)^2 * Real.exp (-r / x)
  have hh (t : ℝ) (ht : t ≠ 0) : HasDerivAt f (g t) t := by
    let q := -r
    have hh := ((((hasDerivAt_const t q).div (hasDerivAt_id' t) ht).exp).const_mul (π^2/r))
    unfold f g
    convert! hh using 1
    unfold q
    simp only [Pi.div_apply]
    field_simp
    ring
  have ht : Tendsto f atTop (𝓝 (π^2/r)) := by
    have hh : Tendsto (fun t : ℝ => -r/t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    simpa [f,Function.comp_def] using (Real.continuous_exp.continuousAt.tendsto.comp hh).const_mul (π^2/r)
  change ∫ x in Ioi 1, g x = _
  rw [integral_Ioi_of_hasDerivAt_of_nonneg ((hh 1 one_ne_zero).continuousAt.continuousWithinAt) (fun x hx => hh x (ne_of_gt (zero_lt_one.trans hx))) (fun x hx => by unfold g; positivity) ht]
  unfold f
  rw [div_one,mul_sub,mul_one]

lemma water_price {x:E4} (hx : x≠0) : retract water x = ↑(Maxwell.Green x*(1-polar (1/4) x)) := by
  let s : E4 → ℝ := fun z => ‖z‖^2/4
  have hs : 0<s x := by have he := norm_pos_iff.mpr hx; unfold s; positivity
  have hh := integral_integral_swap (f:=fun t p => song x p*breeze t p) (gauss_sum x)
  have hb : ∀ p:E4,p≠0 → song x p * water p = ∫ t:ℝ in Ioi 1,song x p*breeze t p := by
    intro p hp; let a := ‖p‖^2; have hr := norm_pos_iff.mpr hp; have ha : 0<a := by unfold a; positivity
    have he : ∫ t:ℝ in Ioi 1,polar t p = Real.exp (-a) /a := by
      unfold polar; simp_rw [mul_comm _ (‖p‖^2), ← neg_mul]; change (∫ t:ℝ in Ioi 1, Real.exp (-a*t)) = _
      rw [integral_exp_mul_Ioi (neg_lt_zero.mpr ha)]; simp
    rw [integral_const_mul]; unfold breeze water; rw [go_real,he]; congr 1; change (↑(Real.exp (-(1*a))) :ℂ)* (↑a:ℂ)⁻¹ = _; push_cast; rw [one_mul]; ring
  have he : feed water x=↑((π^2 / s x) * (1-Real.exp (-s x)):ℝ) := by
    unfold feed; rw [← stale (s x) hs,← go_real]
    apply Eq.trans (b:=∫ p:E4, ∫ t:ℝ in Ioi 1,song x p*breeze t p)
    · refine integral_congr_ae ?_
      have H : ∀ᵐ z:E4,z≠0 := mem_ae_iff.mpr (by change volume ({x:E4 | x≠0}ᶜ)=0; simp)
      exact H.mono hb
    rw [← hh]; refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_); exact gaussian t (zero_lt_one.trans ht) x
  unfold retract
  rw [he]
  unfold Maxwell.Green Maxwell.normal tally height polar
  simp only [← Complex.ofReal_mul]
  unfold s
  congr 1
  rw [show -(1/4 * ‖x‖^2)=-(‖x‖^2/4) by ring]
  have ht := Real.pi_ne_zero
  have hv := norm_pos_iff.mpr hx
  field_simp
  ring

end YM.XSpace.Compat.KP
end
