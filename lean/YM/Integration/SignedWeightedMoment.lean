import YM.RG.Bounded
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.MeanInequalities

/-! Conditional moments for a bounded signed numerator in one positive vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedWeightedMoment
open Function MeasureTheory Filter Set RG
open scoped Classical BigOperators Topology

variable {X E : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

def normalized (μ : Measure X) (p : X → ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (p x / ∫ y, p y ∂μ))

theorem mass_one (μ : Measure X) [IsFiniteMeasure μ] {p : X → ℝ}
    (hp : Envelope p) (h₀ : ∀ x, 0≤p x) (hm : 0 < ∫ x, p x ∂μ) :
    IsProbabilityMeasure (normalized μ p) where
  measure_univ := by
    rw [normalized,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal ((hp.integrable μ).div_const _) (ae_of_all _ fun x => div_nonneg (h₀ x) hm.le),
      integral_div,div_self hm.ne',ENNReal.ofReal_one]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem normalized_integral (μ : Measure X) {p : X → ℝ}
    (hp : Measurable p) (h₀ : ∀ x, 0≤p x) (hm : 0 < ∫ x, p x ∂μ) (f : X → E) :
    ∫ x, f x ∂normalized μ p = (∫ x, p x ∂μ)⁻¹ • ∫ x, p x • f x ∂μ := by
  rw [normalized,integral_withDensity_eq_integral_toReal_smul ((hp.div_const _).ennreal_ofReal)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),← integral_smul]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (div_nonneg (h₀ x) hm.le),smul_smul,div_eq_inv_mul]

omit [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
theorem norm_power_env {f : X → E} (hf : Envelope f) (k : ℕ) :
    Envelope (fun x => ‖f x‖^k) := by
  obtain ⟨c,hc⟩ := hf.cost
  refine ⟨hf.meas.norm.pow_const k,c^k,fun x => ?_⟩
  rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hc x) k

omit [CompleteSpace E] [SecondCountableTopology E] in
/-- Taking the signed mean with the physical positive weight contracts every
natural absolute moment, with unit constant and the same normalization. -/
theorem jensen (μ : Measure X) [IsFiniteMeasure μ] {p : X → ℝ} {f : X → E}
    (hp : Envelope p) (h₀ : ∀ x, 0≤p x) (hm : 0 < ∫ x, p x ∂μ)
    (hf : Envelope f) (k : ℕ) :
    (∫ x, p x ∂μ)*‖(∫ x, p x ∂μ)⁻¹ • ∫ x, p x • f x ∂μ‖^k ≤
      ∫ x, p x * ‖f x‖^k ∂μ := by
  let ν := normalized μ p
  letI : IsProbabilityMeasure ν := mass_one μ hp h₀ hm
  have hnorm : Integrable (fun x => ‖f x‖) ν := by
    obtain ⟨c,hc⟩ := hf.cost
    exact Integrable.of_bound hf.meas.norm.aestronglyMeasurable c (ae_of_all _ fun x => by simpa only [norm_norm] using hc x)
  have J := (convexOn_pow (𝕜:=ℝ) k).map_integral_le (continuous_pow k).continuousOn isClosed_Ici
    (ae_of_all ν fun x => (norm_nonneg (f x) : ‖f x‖ ∈ Ici 0)) hnorm ((norm_power_env hf k).integrable ν)
  have B := (pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm (μ:=ν) f) k).trans J
  change ‖∫ x, f x ∂normalized μ p‖^k ≤ ∫ x, ‖f x‖^k ∂normalized μ p at B
  rw [normalized_integral μ hp.meas h₀ hm f,normalized_integral μ hp.meas h₀ hm (fun x => ‖f x‖^k)] at B
  calc _ ≤ (∫ x, p x ∂μ) * ((∫ x, p x ∂μ)⁻¹ * ∫ x, p x * ‖f x‖^k ∂μ) := mul_le_mul_of_nonneg_left B hm.le
       _ = _ := by rw [← mul_assoc,mul_inv_cancel₀ hm.ne',one_mul]

private theorem product_mean {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ) (ha : ∀ i, 0≤a i) :
    ∏ i, a i ≤ (Fintype.card ι:ℝ)⁻¹ * ∑ i, a i^(Fintype.card ι) := by
  let n := Fintype.card ι
  have hn : (0:ℝ)<n := by exact_mod_cast (Fintype.card_pos (α:=ι))
  have hsum : ∑ _ : ι, (n:ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_inv_cancel₀ hn.ne'
  have B := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ : ι => (n:ℝ)⁻¹) (fun i => a i^n)
    (fun _ _ => inv_nonneg.mpr hn.le) hsum (fun i _ => pow_nonneg (ha i) _)
  simpa only [← Real.rpow_natCast_mul (ha _) n _,mul_inv_cancel₀ hn.ne',Real.rpow_one,Finset.mul_sum] using B

/-- The absolute replicated moment is bounded by the arithmetic mean of the
diagonal absolute moments of the very same factors in the very same vacuum. -/
theorem mixed {ι : Type*} [Fintype ι] [Nonempty ι] (μ : Measure X) [IsFiniteMeasure μ]
    (f : ι → X → ℂ) (hf : ∀ i, Envelope (f i)) :
    ‖∫ x, ∏ i, f i x ∂μ‖ ≤ (Fintype.card ι:ℝ)⁻¹ * ∑ i, ∫ x, ‖f i x‖^(Fintype.card ι) ∂μ := by
  let n := Fintype.card ι
  have ip (i : ι) := (norm_power_env (hf i) n).integrable μ
  calc
    _ ≤ ∫ x, ‖∏ i, f i x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (n:ℝ)⁻¹ * ∑ i, ‖f i x‖^n ∂μ := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
        ((integrable_finsetSum _ fun i _ => ip i).const_mul _)
      filter_upwards with x
      rw [norm_prod]
      exact product_mean (fun i => ‖f i x‖) (fun _ => norm_nonneg _)
    _ = _ := by rw [integral_const_mul,integral_finsetSum _ (fun i _ => ip i)]

end YM.Integration.SignedWeightedMoment
