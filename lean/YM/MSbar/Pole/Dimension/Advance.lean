import YM.MSbar.Pole.Dimension.Direct
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Continuation by shifting, recurrence and ordinary specialization. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Radial
open Function Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
local notation "ω" => volume.restrict (Ioi (0:ℝ))
variable {U : Set E} {p q : Price E} {f : ℝ×E→ℂ}
variable (o : IsOpen U) (c : ContinuousOn p.val U)
    (h : Packet (univ ×ˢ U) (p.back Prod.snd) (Moment q) f)

include o c h
lemma before {x : E} (hx : x∈U) {w : ℂ} (hw : 2 ≤ w.re) : IntegrableOn (fun t:ℝ => f (t,x)*(t:ℂ)^(w-1)) (Ioi (0:ℝ)) := by
  obtain ⟨M,hM⟩:= exists_nat_gt w.re
  have he : ∀ x:E,x∈U → (w+(0:E→L[ℝ] ℂ) x-1).re ∈ Icc 1 (M:ℝ) := fun i _ => by simp; constructor <;> linarith
  have ht := (jBarrel o c 0 w (h.mono (Set.prod_mono (subset_univ _) (fun _ h=>h))) M he).integrable hx
  unfold jKernel at ht; simpa only [zero_apply,add_zero,IntegrableOn] using ht
omit o c in
lemma vanishesAtTop {x : E} (hx : x∈U) (w : ℂ) : Tendsto (fun t:ℝ => f (t,x)*(t:ℂ)^w) atTop (𝓝 0) := by
  obtain ⟨M,hM⟩:= exists_nat_gt w.re
  obtain ⟨C,l,hc,H⟩:= h.values (M+1)
  refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    ((tendsto_const_nhds (x:=C*p x^l)).div_atTop (g:=fun t:ℝ=>t) (tendsto_id)))
  filter_upwards [eventually_ge_atTop 1] with t ht; have hv := zero_lt_one.trans_le ht
  have he : t ^ w.re ≤ t^M := by simpa using Real.rpow_le_rpow_of_exponent_le ht hM.le
  change ‖f (t,x)*(t:ℂ)^w‖ ≤ _; rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv, le_div_iff₀ hv,mul_assoc]
  refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he hv.le) (norm_nonneg _)) (le_trans ?_ (H (t,x) (mem_prod.mpr ⟨mem_univ _,hx⟩)))
  rw [← pow_succ]
  change ‖f (t,x)‖ * _ ≤ ‖f (t,x)‖ * ((1+|t|)*q x)^_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv.le ((show t ≤ 1+|t| by rw [abs_of_nonneg hv.le]; simp).trans (le_mul_of_one_le_right (by positivity) (q.large _))) _) (norm_nonneg _)

variable [FiniteDimensional ℝ E]
-- valid in the initial half-plane used to start dim reg (two-dimensional buffer)
lemma shift_j {x : E} (hx : x∈U) (he : EvenOn U f) {w : ℂ} (hw : 2≤w.re) :
    j (fun r : ℝ=> higher f (r,x)) (w+2) = j (fun r => f (r,x)) w := by
  let F (t : ℝ) := f (t,x); let X (t : ℝ) := F t*(t:ℂ)^(w-1); let Z (t : ℝ) := F t * (t:ℂ)^w
  let Y (t : ℝ) := higher f (t,x)*(t:ℂ)^((w+2)-1)
  have hv : Integrable X ω := before o c h hx hw
  have hY : Integrable Y ω := before o c (smooth o c h he) hx (by simp; linarith)
  have hw' : 0<w.re := zero_lt_two.trans_le hw
  have hw₀ : w≠0 := by rintro rfl; simp at hw'
  have h₁ : ContinuousWithinAt Z (Ici 0) 0 := ((letter_read h 0 hx).continuousAt.mul
    (Complex.continuousAt_ofReal_cpow_const 0 w (Or.inl hw'))).continuousWithinAt
  have hZ (t : ℝ) (ht: 0<t) : HasDerivAt Z (w*X t-2*Y t) t := by
    have ha := (letter_read h t hx).mul (hasDerivAt_ofReal_cpow_const ht.ne' hw₀)
    apply ha.congr_deriv
    unfold X Y F
    rw [show w+2-1 = w+1 by ring,Complex.cpow_add _ _ (by exact_mod_cast ht.ne'),Complex.cpow_one]
    have hh := formula h he t hx
    simp_rw [Complex.real_smul] at hh
    change letter f (t,x)*(t:ℂ)^w+_= _
    simp only [Complex.ofReal_neg,Complex.ofReal_inv,Complex.ofReal_ofNat] at hh
    linear_combination (2 * ((t:ℂ)^w)) * hh
  have hz := integral_Ioi_of_hasDerivAt_of_tendsto h₁ (fun t ht => hZ t ht) ((hv.const_mul w).sub (hY.const_mul 2)) (vanishesAtTop h hx w)
  have ha : Z 0=0 := by simp [Z,hw₀]
  rw [ha,sub_zero] at hz
  change (∫ t : ℝ, w*X t-2*Y t ∂ω)=0 at hz; rw [integral_sub (hv.const_mul w) (hY.const_mul 2),integral_const_mul,integral_const_mul] at hz
  have hb : w/2 ≠ 0 := div_ne_zero hw₀ (by norm_num)
  have hm : Complex.Gamma (w/2)≠0 := Complex.Gamma_ne_zero_of_re_pos (by simp [hw'])
  unfold j
  change 2/_*(∫ t,Y t ∂ω)=2/_*(∫ t,X t ∂ω)
  rw [show (w+2)/2=w/2+1 by ring,Complex.Gamma_add_one _ hb]
  field_simp
  linear_combination - hz

lemma extractAtZero {x : E} (hx : x∈U) (he : EvenOn U f) :
    j (fun r => higher f (r,x)) 2 = f (0,x) := by
  let Y (t:ℝ) := higher f (t,x)*(t:ℂ)^((2:ℂ)-1); let F (t:ℝ) := f (t,x)
  have hY : Integrable Y ω := before o c (smooth o c h he) hx (by simp)
  have hh : (∫ t:ℝ,-(2:ℂ)*Y t ∂ω)=0-f (0,x) := by
    refine integral_Ioi_of_hasDerivAt_of_tendsto (f:=F) (letter_read h 0 hx).continuousAt.continuousWithinAt
      (fun t ht => (letter_read h t hx).congr_deriv ?_) (hY.const_mul _) ?_
    · have hp := formula h he t hx
      unfold Y; norm_num
      simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_inv,Complex.ofReal_ofNat] at hp; linear_combination 2*hp
    simpa only [Complex.cpow_zero,mul_one] using vanishesAtTop h hx 0
  rw [integral_const_mul] at hh; unfold j
  change 2/_*_ = _
  norm_num [← neg_mul,zero_sub, Y] at hh ⊢; linear_combination - hh
end YM.MSbar.Pole.Radial
