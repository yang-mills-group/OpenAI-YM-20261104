import YM.Source.Construction
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Analytic facts about the actual finite Wilson integrals

Here the variable is the *bare* inverse coupling itself, and there is no assertion that this
parameter tunes the desired coupling at the bottom of a recursion. Entire continuation of
unnormalized integrals; elementary (volume dependent) zero-free neighborhood and analytic
normalized expectation for a fixed incoming cylinder. Keeping a cylinder fixed in this lemma
should not be confused with proving analyticity for parameter-dependent calibrated cylinder
coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt
open Set Function Filter MeasureTheory Wilson Lattice
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}

/-- Not a volume independent bound. -/
def rawCap (n : Side) : ℝ := 1 + 2 * (Fintype.card (Face (Per n)):ℝ)

lemma rawCap_pos (n : Side) : 0 < rawCap n := by unfold rawCap; positivity

lemma energy_le_rawCap (U : Config G n) : energy U ≤ rawCap n := by
  unfold energy rawCap
  exact (Finset.sum_le_sum (g:=fun _ => (2:ℝ)) (fun p _ => (G.price_range (faceValue U p)).2)).trans
    (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; linarith)

def complexWeight (z : ℂ) (U : Config G n) := Complex.exp (-z * (energy U:ℂ))
def complexPriorIntegral (F : Config G n → ℂ) (z : ℂ) := ∫ U, complexWeight z U * F U ∂prior G n
def complexPartition (G : Gauge) (n : Side) (z : ℂ) := ∫ U : Config G n, complexWeight z U ∂prior G n
def complexMoment (F : Config G n → ℂ) (z : ℂ) := complexPriorIntegral F z / complexPartition G n z

lemma complexWeight_cont (z : ℂ) : Continuous (complexWeight (G:=G) (n:=n) z) := by unfold complexWeight; fun_prop

lemma complexPrior_differentiable {F : Config G n → ℂ} (hf : Continuous F) :
    Differentiable ℂ (complexPriorIntegral F) := by
  let μ := prior G n
  let φ (z : ℂ) (U : Config G n) := complexWeight z U * F U
  let dφ (z : ℂ) (U : Config G n) := complexWeight z U * (-(energy U:ℂ)) * F U
  intro z
  have hφ w U : HasDerivAt (fun x : ℂ => φ x U) (dφ w U) w := by
    simpa only [φ, dφ, complexWeight, neg_one_mul] using ((((hasDerivAt_id' w).fun_neg.mul_const ((energy U):ℂ)).cexp).mul_const (F U))
  obtain ⟨M,hM⟩ := (isCompact_range hf.norm).bddAbove
  have hF U : ‖F U‖ ≤ M := hM ⟨U,rfl⟩
  have hm : 0 ≤ M := le_trans (norm_nonneg _) (hF (1:Config G n))
  let K := Real.exp ((‖z‖+1)*rawCap n)*rawCap n*M
  have hb U {w : ℂ} (hw : w ∈ Metric.ball z 1) : ‖dφ w U‖ ≤ K := by
    have hW := hw; rw [Metric.mem_ball, dist_eq_norm] at hW
    have hw_z : ‖w‖ ≤ ‖z‖ + 1 := by linarith [norm_sub_norm_le w z]
    have hz : |w.re| ≤ ‖z‖+1 := (Complex.abs_re_le_norm w).trans hw_z
    unfold dφ K complexWeight; rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (energy_nonneg _), Complex.norm_exp]
    have hex : Real.exp (-w * (energy U : ℂ)).re ≤ Real.exp ((‖z‖+1)*rawCap n) := Real.exp_le_exp.mpr (by
      rw [neg_mul, Complex.neg_re, Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,mul_zero,sub_zero]
      refine (neg_le_abs (w.re * energy U)).trans ?_; rw [abs_mul,abs_of_nonneg (energy_nonneg _)]; exact

        (mul_le_mul hz (energy_le_rawCap U) (energy_nonneg _) (by positivity)) )
    exact mul_le_mul (mul_le_mul hex (energy_le_rawCap U) (energy_nonneg _) (by positivity)) (hF U) (norm_nonneg _) (by positivity [rawCap_pos n])
  have hμ (w : ℂ) : Continuous (φ w) := (complexWeight_cont w).mul hf
  have hd (w : ℂ) : Continuous (dφ w) := (complexWeight_cont w |>.mul (Complex.continuous_ofReal.comp energy_cont).neg).mul hf
  exact ((hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound:=fun _ => K) (F:=φ) (μ:=μ)
    (Metric.ball_mem_nhds z one_pos)
    (Eventually.of_forall fun w => (hμ w).aestronglyMeasurable)
    ((hμ z).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hd z).aestronglyMeasurable) (Eventually.of_forall (fun U w hw => hb U hw))
    (integrable_const K) (Eventually.of_forall (fun U w _ => hφ w U))).2).differentiableAt


lemma complexPartition_eq_unit : complexPartition G n = complexPriorIntegral (fun _ : Config G n => 1) := by
  ext z; simp only [complexPartition,complexPriorIntegral,mul_one]

@[simp] lemma weight_real (β : ℝ) (U : Config G n) : complexWeight (β:ℂ) U = (bare β U : ℂ) := by
  simp only [complexWeight,bare,Complex.ofReal_exp, Complex.ofReal_mul,Complex.ofReal_neg]

@[simp] lemma partition_real (β : ℝ) : complexPartition G n (β:ℂ) = (partition G n β : ℂ) := by
  simp only [complexPartition,weight_real,partition]
  exact integral_ofReal (𝕜:=ℂ)

def elementaryRadius (n : Side) : ℝ := (8 * rawCap n)⁻¹

lemma elementaryRadius_pos (n : Side) : 0 < elementaryRadius n := by unfold elementaryRadius; positivity [rawCap_pos n]

lemma weight_difference {β : ℝ} {z : ℂ} (hz : ‖z-(β:ℂ)‖ ≤ elementaryRadius n) (U : Config G n) :
    ‖complexWeight z U - complexWeight (β:ℂ) U‖ ≤ bare β U / 2 := by
  let q := -(z-(β:ℂ)) * (energy U:ℂ)
  have hq : ‖q‖ ≤ 1/8 := by
    unfold q; rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (energy_nonneg _)]
    have hh := mul_le_mul hz (energy_le_rawCap U) (energy_nonneg U) (elementaryRadius_pos n).le
    exact hh.trans_eq (by unfold elementaryRadius; field_simp [(rawCap_pos n).ne'])
  rw [complexWeight,show -z*(energy U:ℂ)= -(β:ℂ)*(energy U:ℂ)+q from by unfold q; ring,
    Complex.exp_add]
  change ‖complexWeight (β:ℂ) U * Complex.exp q - complexWeight (β:ℂ) U‖ ≤ _
  rw [show complexWeight (β:ℂ) U * Complex.exp q - complexWeight (β:ℂ) U = complexWeight (β:ℂ) U * (Complex.exp q-1) from by ring,
    norm_mul,weight_real,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (bare_pos _ _).le]
  have h := Complex.norm_exp_sub_one_le (show ‖q‖≤1 from by linarith)
  nlinarith [bare_pos β U]

/-- An elementary volume-dependent neighborhood for the normalized moments. -/
lemma elementary_nonzero {β : ℝ} {z : ℂ} (hz : ‖z-(β:ℂ)‖ ≤ elementaryRadius n) :
    complexPartition G n z ≠ 0 := by
  have hi w : Integrable (complexWeight (G:=G) (n:=n) w) (prior G n) :=
    (complexWeight_cont w).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h : ‖complexPartition G n z - complexPartition G n (β:ℂ)‖ ≤ partition G n β / 2 := by
    unfold complexPartition partition
    rw [← integral_sub (hi z) (hi (β:ℂ)), ← integral_div]
    exact (norm_integral_le_integral_norm _).trans (integral_mono ((hi z|>.sub (hi (β:ℂ))).norm)
      ((bare_integrable β).div_const _) (fun U => weight_difference hz U))
  rw [partition_real] at h
  intro he; rw [he,zero_sub,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (partition_pos β)] at h
  linarith [partition_pos (G:=G) (n:=n) β]

lemma elementary_analytic {β : ℝ} {F : Config G n → ℂ} (h : Continuous F) :
    AnalyticOnNhd ℂ (complexMoment F) (Metric.ball (β:ℂ) (elementaryRadius n)) := by
  intro z hz
  change AnalyticAt ℂ (complexPriorIntegral F / complexPartition G n) z
  have hu := complexPrior_differentiable h
  have hZ : ‖z-(β:ℂ)‖ ≤ elementaryRadius n := dist_eq_norm z (β:ℂ) ▸ (Metric.mem_ball.mp hz).le
  refine (hu.analyticAt z).div ?_ (elementary_nonzero hZ)
  rw [complexPartition_eq_unit]; exact (complexPrior_differentiable continuous_const).analyticAt z

lemma moment_eq_real {β : ℝ} {F : Config G n → ℂ} (h : Continuous F) :
    complexMoment F (β:ℂ) = moment β F := by
  rw [moment_formula _ _ (continuous_integrable β h)]
  simp only [complexMoment,partition_real,complexPriorIntegral,weight_real,div_eq_mul_inv]
  ring
end YM.UVExt
