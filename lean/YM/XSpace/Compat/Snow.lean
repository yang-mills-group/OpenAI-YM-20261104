import YM.Further.FREE_COVARIANCE_KP.KP.Snow
import YM.Further.FREE_COVARIANCE_KP.KP.House
import YM.Further.FREE_COVARIANCE_KP.KP.Plain
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Additive compatibility closure from pinned Oct15 ancestry.
Current baseline definitions are reused; extracted declaration text is unchanged.
Prepared for independent checking; no successful build is claimed here. -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Compat.KP
open YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace
variable {ι : Type*}

def snow (t : ℝ) (p:E4) := arctic (t⁻¹ • p)

lemma basin : Integrable arctic := by
  have h := integrable_one_add_norm (μ := (volume:Measure E4)) (r:= ((5:ℕ):ℝ)) (by norm_num [E4,YM.Axis])
  convert! h using 1
  funext p
  unfold arctic
  rw [Real.rpow_neg (by positivity),Real.rpow_natCast]

lemma snow_ready {t : ℝ} (ht : 0<t) : Integrable (snow t) := basin.comp_smul (inv_ne_zero ht.ne')

lemma snow_melts {t : ℝ} (ht : 0<t) : ∫ p, snow t p = t^4 * ∫ p, arctic p := by unfold snow; rw [Measure.integral_comp_smul]; simp [E4,YM.Axis,abs_of_pos ht]

lemma snow_radial {p:E4} {t:ℝ} (ht : 0<t) : snow t p = t^5 * ((t+‖p‖)^5)⁻¹ := by
  unfold snow arctic
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
  field_simp

lemma snow_ok (t p) : 0≤snow t p := by unfold snow arctic; positivity

private def frost : ContDiffBump (0:E4) := ⟨1,2,by norm_num,by norm_num⟩

def chess (p:E4) : ℂ := ↑(frost p)

lemma chess_smooth : ContDiff ℝ ∞ chess := Complex.ofRealCLM.contDiff.comp frost.contDiff

lemma chess_low {p : E4} (h : ‖p‖≤1) : chess p=1 := by rw [chess,frost.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr h),ofReal_one]

lemma chess_high {p : E4} (h : 2≤‖p‖) : chess p=0 := by
  unfold chess
  rw [← Complex.ofReal_zero]
  congr
  by_contra w
  have hh : p∈ball (0:E4) frost.rOut := frost.support_eq ▸ (show p∈Function.support frost from w)
  exact h.not_gt (mem_ball_zero_iff.mp hh)

lemma chess_price : Weight (ι:=ι) whole 0 (fun _ => chess) := by
  let U : Window := ⟨ball 0 3 ∩ whole.look,isOpen_ball.inter whole.ok,fun h => whole.hole h.2⟩
  let V := rim 2 (by norm_num)
  have hb : Weight (ι:=ι) U 0 (fun _=>chess) := (Plain.sample _ chess_smooth).zero_power (R:=3) (by norm_num) (fun i h => (mem_ball_zero_iff.mp h.1).le)
  have he : Weight (ι:=ι) V 0 (fun _=>chess) := (Weight.vanish _ _).stay (fun i p hp => (chess_high (show 2<‖p‖ from hp).le).symm)
  refine blend hb he fun i hi => ?_; by_cases h : ‖i‖ <3; exact Or.inl ⟨mem_ball_zero_iff.mpr h,hi⟩; exact Or.inr (show 2<‖i‖ by linarith)

abbrev Chip := {t : ℝ // 0<t}

def ore (a : ι × Chip) (p : E4) := chess (a.2.val⁻¹ • p)

lemma ore_clean (a : ι×Chip) : ContDiff ℝ ∞ (ore a) := chess_smooth.comp (contDiff_id.const_smul _)

lemma ore_quote : Weight whole 0 (ore (ι:=ι)) := by
  refine ⟨fun a => (ore_clean a).contDiffOn,fun n => ?_⟩
  obtain ⟨C,hC,H⟩ := (chess_price (ι:=Unit)).quotes n
  refine ⟨C,hC,fun i p hp => ?_⟩
  let t := i.2.val⁻¹; have ht : 0<t := inv_pos.mpr i.2.property
  have hx := whole.out hp
  have hh : t • p ∈ whole := (show t • p ≠ 0 from smul_ne_zero ht.ne' hx)
  specialize H () _ hh; rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht] at H
  unfold ore
  rw [iteratedFDeriv_comp_const_smul _ (chess_smooth.of_le (by exact_mod_cast (le_top : (↑n:ℕ∞)≤⊤))),norm_smul,Real.norm_eq_abs]
  change |t^n| * _ ≤ _
  rw [abs_of_pos (pow_pos ht _)]
  apply (mul_le_mul_of_nonneg_left H (pow_pos ht n).le).trans_eq; rw [zero_sub,zpow_neg,zpow_neg,zpow_natCast,zpow_natCast,mul_pow]; field_simp

lemma ore_full {a : ι × Chip} {p:E4} (h : ‖p‖≤a.2.val) : ore a p=1 := by
  apply chess_low; rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr a.2.property),mul_comm,← div_eq_mul_inv,div_le_one a.2.property]; exact h

lemma ore_dry {a : ι × Chip} {p:E4} (h : 2*a.2.val≤‖p‖) : ore a p=0 := by
  apply chess_high; rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr a.2.property),mul_comm,← div_eq_mul_inv]; exact (le_div_iff₀ a.2.property).2 h

def flake (f : ι→E4→ℂ) (a : ι × Chip) (p:E4) : ℂ := ore a p * f a.1 p

def shell (f : ι→E4→ℂ) (a : ι × Chip) (p:E4) : ℂ := (1-ore a p)*f a.1 p

variable {m : ℕ} {f : ι→ E4→ℂ}

lemma flake_paid (hf : Weight whole (m:ℤ) f) : ∃ C : ℝ, 0≤C ∧ ∀ a : ι × Chip,∀ p:E4,p≠0 → ‖flake f a p‖ ≤ C*a.2.val^m*snow a.2.val p := by
  have h := ore_quote.times (hf.reindex (@Prod.fst ι Chip)); obtain ⟨C,hC,H⟩ := h.quotes 0
  refine ⟨C*2^m*3^5,by positivity,fun a p hp => ?_⟩; let t := a.2.val; have ht : 0<t := a.2.property
  by_cases hd : 2*t≤‖p‖
  · rw [flake,ore_dry hd,zero_mul,norm_zero]; have he := snow_ok a.2.val p; change 0≤C*_*_^_*t^_*snow t p; apply mul_nonneg _ he; positivity
  have hb : ((3:ℝ)^5)⁻¹ ≤ snow t p := by
    unfold snow arctic; apply (inv_le_inv₀ (by positivity) (by positivity)).2; gcongr
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht),mul_comm,← div_eq_mul_inv]; have hh := (div_lt_iff₀ ht).mpr (lt_of_not_ge hd); linarith
  have hs : 1≤ 3^5*snow t p := by have hh := (inv_le_iff_one_le_mul₀ (by positivity : (0:ℝ)<3^5)).1 hb; linarith
  calc
    _ ≤ C*‖p‖^m := by simpa only [norm_iteratedFDeriv_zero,flake,comp_apply,Nat.cast_zero,zero_add,sub_zero,zpow_natCast] using H a p hp
    _ ≤ C*(2*t)^m := by gcongr; exact le_of_lt (lt_of_not_ge hd)
    _ ≤ (C*(2*t)^m)*(3^5*snow t p) := le_mul_of_one_le_right (by positivity) hs
    _ = _ := by unfold t; rw [mul_pow]; ring

lemma shell_spare {k : ℤ} (hf : Weight whole k f) : Weight whole k (shell f) := by
  have h := ((Weight.spare (ι:=ι×Chip) whole 1).diff ore_quote).times (hf.reindex Prod.fst); rw [zero_add] at h; exact h

lemma shell_no (f : ι→E4→ℂ) (a:ι × Chip) {p : E4} (hp : ‖p‖<a.2.val) : shell f a =ᶠ[𝓝 p] fun _=>0 := by
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hp)] with x hx; rw [shell,ore_full (mem_ball_zero_iff.mp hx).le]; simp

lemma shell_smooth {k : ℤ} (hf : Weight whole k f) (a : ι×Chip) : ContDiff ℝ ∞ (shell f a) := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_; by_cases h : x=0
  · subst x; exact contDiffAt_const.congr_of_eventuallyEq (shell_no f a (by simpa using a.2.property))
  exact ((shell_spare hf).smooth a).contDiffAt (whole.ok.mem_nhds h)

lemma shell_paid (hf : Weight whole (m:ℤ) f) (hg : Weight whole (-5) f) {n : ℕ} (hn : n ≤ m+5) : ∃ C : ℝ, 0≤C ∧ ∀ a : ι×Chip,∀ p:E4,
    ‖iteratedFDeriv ℝ n (shell f a) p‖ ≤ C*(a.2.val^5)⁻¹*snow a.2.val p := by
  obtain ⟨C,hC,H⟩ := (shell_spare hf).quotes n; obtain ⟨B,hB,K⟩ := (shell_spare hg).quotes n
  let L := max C B; have hL : 0≤L := hC.trans (le_max_left ..)
  refine ⟨L*2^5,by positivity,fun a p => ?_⟩; let t := a.2.val; have ht : 0<t := a.2.property
  by_cases h : t ≤ ‖p‖; swap
  · rw [((shell_no f a (lt_of_not_ge h)).iteratedFDeriv ℝ n).eq_of_nhds]; have he := snow_ok t p
    cases n <;> simp only [iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero] <;> (change 0 ≤ L*2^5*(t^5)⁻¹*snow t p; positivity)
  have hr := ht.trans_le h
  have hb : p∈whole := norm_pos_iff.mp hr
  have hw : ‖iteratedFDeriv ℝ n (shell f a) p‖ ≤ L*‖p‖^(-5:ℤ) := by
    by_cases hy : 1≤‖p‖
    · apply (K _ _ hb).trans; apply mul_le_mul (le_max_right ..) (zpow_le_zpow_right₀ hy (by omega)) (by positivity) hL
    apply (H _ _ hb).trans
    apply mul_le_mul (le_max_left ..) _ (by positivity) hL
    rw [← inv_le_inv₀ (by positivity) (by positivity)]
    have hR : 1≤‖p‖⁻¹ := (one_le_inv₀ hr).mpr (le_of_lt (lt_of_not_ge hy))
    simp only [← inv_zpow]
    exact zpow_le_zpow_right₀ hR (by omega)
  refine hw.trans ?_
  change _ ≤ L*2^5*(t^5)⁻¹ * snow t p; rw [snow_radial ht]
  rw [zpow_neg,zpow_ofNat]
  have he : ‖p‖^5 ≥ ((t+‖p‖)/2)^5 := by gcongr; linarith
  field_simp; unfold L at *; nlinarith

end YM.XSpace.Compat.KP
end
