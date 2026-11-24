import YM.XSpace.Compat.Snow
import YM.XSpace.Compat.Native
import YM.Further.FREE_COVARIANCE_KP.KP.Hill
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-! Additive compatibility closure from pinned Oct15 ancestry.
Current baseline definitions are reused; extracted declaration text is unchanged.
Prepared for independent checking; no successful build is claimed here. -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Compat.KP
open YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory VectorFourier
open scoped Topology ContDiff BigOperators InnerProductSpace FourierTransform Real
variable {ι : Type*} {f : ι→E4→ℂ} {l : ℕ}

private lemma pole_ae : ∀ᵐ x:E4,x∈whole := mem_ae_iff.mpr (by change volume (({0}ᶜ:Set E4)ᶜ)=0; rw [compl_compl]; simp)

lemma dump_nonneg : 0≤dump := integral_nonneg fun p => by unfold arctic; positivity

lemma flake_budget (hf : Weight whole (l:ℤ) f) : ∃ C : ℝ, 0≤C ∧ ∀ a : ι × Chip, Integrable (flake f a) ∧ ∫ p:E4, ‖flake f a p‖ ≤ C*a.2.val^(l+4) := by
  obtain ⟨A,hA,H⟩ := flake_paid hf; refine ⟨A*dump,mul_nonneg hA dump_nonneg,fun a => ?_⟩
  let t := a.2.val; have ht : 0<t := a.2.property
  have hh := (snow_ready ht).const_mul (A*t^l)
  have he : ∀ᵐ p:E4, ‖flake f a p‖≤ A*t^l*snow t p := pole_ae.mono (fun i hi => H _ _ hi)
  have hb := hh.mono' (pore_meas (show ContinuousOn (flake f a) whole.look from (ore_clean a).continuous.continuousOn.mul (hf.smooth a.1).continuousOn)) he
  refine ⟨hb,(integral_mono_ae hb.norm hh he).trans_eq ?_⟩; rw [integral_const_mul,snow_melts ht]; unfold dump t; ring

lemma shell_budget (hf : Weight whole (l:ℤ) f) (hg : Weight whole (-5) f) {n : ℕ} (hn : n ≤ l+5) :
    ∃ C : ℝ, 0≤C ∧ ∀ a : ι × Chip, let D (p:E4) := ‖iteratedFDeriv ℝ n (shell f a) p‖; Integrable D ∧ ∫ p:E4, D p ≤ C*a.2.val⁻¹ := by
  obtain ⟨A,hA,H⟩ := shell_paid hf hg hn; refine ⟨A*dump,mul_nonneg hA dump_nonneg,fun a => ?_⟩; intro D
  let t := a.2.val; have ht : 0<t := a.2.property
  have hh := (snow_ready ht).const_mul (A*(t^5)⁻¹)
  have hD := (shell_smooth hf a).continuous_iteratedFDeriv (show (n:ℕ∞ω)≤∞ by exact_mod_cast (le_top : (↑n:ℕ∞)≤⊤))
  have he := hh.mono' hD.aestronglyMeasurable (Eventually.of_forall (H a)); refine ⟨he.norm,(integral_mono he.norm hh (H a)).trans_eq ?_⟩
  rw [integral_const_mul,snow_melts ht]; change A*(t^5)⁻¹*(t^4*dump)=_*t⁻¹; field_simp

lemma turnout (f : ι→E4→ℂ) (a : ι×Chip) : shell f a+flake f a=f a.1 := by funext p; simp only [Pi.add_apply,shell,flake]; ring

lemma shell_good (hf : Weight whole (l:ℤ) f) (hg : Weight whole (-5) f) (a : ι×Chip) : Integrable (shell f a) := by
  obtain ⟨C,hC,H⟩ := shell_budget hf hg (Nat.zero_le _)
  have hh := (H a).1
  simp only [norm_iteratedFDeriv_zero] at hh
  exact hh.mono' (shell_smooth hf a).continuous.aestronglyMeasurable (Eventually.of_forall fun x=>le_refl _)

lemma asset_good (hf : Weight whole (l:ℤ) f) (hg : Weight whole (-5) f) (i) : Integrable (f i) := by
  let a : ι × Chip := (i,⟨1,zero_lt_one⟩); obtain ⟨C,hC,H⟩ := flake_budget hf; exact turnout f a ▸ (shell_good hf hg a).add (H a).1

lemma meal_le (f:E4→ℂ) (x:E4) : ‖feed f x‖ ≤ ∫ p:E4, ‖f p‖ := by unfold feed; apply (norm_integral_le_integral_norm ..).trans_eq; simp [song_fee]

lemma meal_sum {f g:E4→ℂ} (hf : Integrable f) (hg : Integrable g) (x:E4) : feed (f+g) x=feed f x+feed g x := by
  unfold feed
  simp_rw [Pi.add_apply,mul_add]
  rw [integral_add (meal_ok hf x) (meal_ok hg x)]

def shade : E4 →L[ℝ] E4 →L[ℝ] ℝ := -height • (innerSL ℝ)

lemma height_pos : 0< height := by unfold height; positivity

lemma circle_phase (p x : E4) : ((𝐞 (-(shade p x))):ℂ) = song x p := by
  unfold song shade; rw [Real.fourierChar_apply,london_at]; congr 1
  change ↑(2*Real.pi* -(-height*⟪p,x⟫_ℝ)) * I= _; rw [real_inner_comm p]
  unfold height; have hπ := Real.pi_pos
  rw [show 2*Real.pi * -(-((2*Real.pi)⁻¹)*⟪p,x⟫_ℝ) = ⟪p,x⟫_ℝ from by field_simp]; ring

lemma shade_drops (f:E4→ℂ) (x:E4) : fourierIntegral 𝐞 volume shade.toLinearMap₁₂ f x=feed f x := by
  unfold feed fourierIntegral; congr 1; ext1 p; change ((𝐞 (-(shade p x))):ℂ)*f p = _; rw [circle_phase]

lemma sky_pay (hf : Weight whole (l:ℤ) f) (hg : Weight whole (-5) f) : ∃ C : ℝ, 0≤C ∧ ∀ a : ι×Chip,∀ x:E4,x≠0 →
    ‖feed (shell f a) x‖*‖x‖^(l+5) ≤ C*a.2.val⁻¹ := by
  let n := l+5
  choose B hB H using fun i : Fin (n+1) => shell_budget hf hg (Nat.le_of_lt_succ i.isLt)
  let P := Finset.range 1 ×ˢ Finset.range (n+1)
  let K := ∑ j : Fin (n+1),B j
  have hK : 0≤K := Finset.sum_nonneg fun j _ => hB _
  have hL := height_pos
  refine ⟨2^n * P.card * K/(height^n),by positivity,fun a x hx => ?_⟩
  have hI (i j : ℕ) (hi : (↑i:ℕ∞) ≤ 0) (hj : (↑j:ℕ∞) ≤ ↑n) : Integrable (fun v => ‖v‖ ^i * ‖iteratedFDeriv ℝ j (shell f a) v‖) := by
    have hh : i=0 := by simpa using hi
    simpa only [hh,pow_zero,one_mul] using (H ⟨j,by apply Nat.lt_succ_of_le; exact_mod_cast hj⟩ a).1
  let v := ‖x‖⁻¹ • x; have hx' := norm_pos_iff.mpr hx
  have hh := pow_mul_norm_iteratedFDeriv_fourierIntegral_le shade ((shell_smooth hf a).of_le (show (↑(n : ℕ∞):ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr le_top)) hI (show (↑(0:ℕ):ℕ∞) ≤ 0 from le_rfl) (show (↑n:ℕ∞) ≤ ↑n from le_rfl) v x
  have hv : ‖v‖=1 := by simp [v,norm_smul,hx]
  have hS : |shade v x| = height * ‖x‖ := by
    change |-height*⟪v,x⟫_ℝ|=_
    unfold v
    rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
    rw [abs_mul,abs_neg,abs_of_pos hL,abs_of_nonneg (by positivity)]
    field_simp
  rw [norm_iteratedFDeriv_zero,hv,hS,shade_drops] at hh
  simp only [Nat.cast_zero,pow_zero,one_pow,one_mul,mul_one,zero_add,mul_zero,mul_pow] at hh
  let t := a.2.val; have ht : 0<t := a.2.property
  have hb : (∑ p∈P, ∫ v:E4, ‖v‖^p.1 * ‖iteratedFDeriv ℝ p.2 (shell f a) v‖) ≤ P.card*(K*t⁻¹) := by
    rw [show (P.card:ℝ)*_=∑ _∈P,K*t⁻¹ from by simp]; refine Finset.sum_le_sum fun i hi => ?_
    obtain ⟨h1,h2⟩ := Finset.mem_product.mp hi
    rw [show i.1=0 by simpa using h1]
    simp only [pow_zero,one_mul]
    apply ((H ⟨i.2,Finset.mem_range.mp h2⟩ a).2).trans
    gcongr
    exact Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ _)
  change _ ≤ (_/(height^n))*t⁻¹; rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hL n)]; change ‖feed _ x‖*_ ^ n*_ ≤ _
  have he := hh.trans (mul_le_mul_of_nonneg_left hb (by positivity : 0≤(2:ℝ)^n)); linarith

lemma night_pay (hf : Weight whole (l:ℤ) f) (hg : Weight whole (-5) f) : ∃ C : ℝ, 0≤C ∧ ∀ i,∀ x:E4,x≠0 →
    ‖feed (f i) x‖ ≤ C*(‖x‖^(l+4))⁻¹ := by
  obtain ⟨B,hB,H⟩ := sky_pay hf hg; obtain ⟨C,hC,h⟩ := flake_budget hf
  refine ⟨B+C,by positivity,fun i x hx => ?_⟩
  let r := ‖x‖; have hr : 0<r := norm_pos_iff.mpr hx
  let a : ι × Chip := (i,⟨r⁻¹,inv_pos.mpr hr⟩)
  have hb : ‖feed (shell f a) x‖ ≤ B*(r^(l+4))⁻¹ := by
    have hh := H a x hx
    rw [pow_succ] at hh
    change _*(_*r) ≤ B*r⁻¹⁻¹ at hh
    rw [inv_inv,← mul_assoc] at hh
    rw [← div_eq_mul_inv,le_div_iff₀ (by positivity : 0<r^(l+4))]
    exact (le_of_mul_le_mul_right hh hr)
  have hd : ‖feed (flake f a) x‖ ≤ C*(r^(l+4))⁻¹ := by apply (meal_le ..).trans; rw [← inv_pow]; exact (h a).2
  rw [show f i=shell f a+flake f a from (turnout f a).symm, meal_sum (shell_good hf hg a) (h a).1]
  rw [add_mul]
  exact (norm_add_le ..).trans (add_le_add hb hd)

end YM.XSpace.Compat.KP
end
