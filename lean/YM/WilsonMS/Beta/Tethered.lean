import YM.WilsonMS.Beta.HeatPapers
/-!
# Integrating on the finite heat envelope and tracing the mark

Prove required domination with *no assumptions* on relative scales (argument
r in this shell contribution is in [0,1]). Integral_add etc don't work
on arbitrary formal objects without such a verification.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BetaValue
open Function Filter Set Finset MeasureTheory Metric
open LoopRank Lattice MS Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect
  Native
open Book Convolve City Logarithm Signal Landau.Detect.Mark Wind High Knobs
open LogTime LogTime.IntervalFamily Outlook Land Arc Wire Rock Path Oceans Plum Alps Garment Color
  Pearl
open Arts Motif Halo
open _root_.YM.PertExtension
open RG FormalOPE FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open Complex (I)
open HeatPapers
open scoped Topology ContDiff BigOperators
variable (p q : QP) (a b : Axis) (t r : ℝ)

abbrev mplane : Measure QP :=
  covMeasure Axis

abbrev mint : Measure ℝ :=
  volume.restrict (Ioc 0 1)

instance cash_m : IsFiniteMeasure mint := by
  unfold mint
  infer_instance

lemma brush_funded (f : QP → ℝ) (h : HeatPapers.Sheet f) :
    Integrable (fun q : QP => City.brush 1 q * f q) mplane := by
  simpa [City.brush] using Pα f h 1 zero_lt_one

lemma bond (F : QP → ℝ) (hp : HeatPapers.Sheet F) :
    Integrable (μ := mplane.prod mint) (fun v => Pill v.2 p v.1 * F v.1) := by
  have he : Integrable (μ := mplane.prod mint) (fun v => ‖City.brush 1 v.1 * F v.1‖) := by
    have h := (brush_funded F hp).norm
    simpa only [mul_one] using
      Integrable.mul_prod h (show Integrable _ mint from (integrable_const (1 : ℝ)))
  have hP : Continuous fun v : QP × ℝ => Pill v.2 p v.1 * F v.1 := by
    unfold Pill City.brush Momentum.sq
    apply Continuous.mul (by fun_prop)
    exact (Temp F hp).comp continuous_fst
  refine he.mono' hP.aestronglyMeasurable ?_
  have ht : ∀ᵐ v ∂mplane.prod mint, v.2 ∈ Set.Ioc 0 1 := by
    apply
      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := mplane) (ν :=
            mint)).tendsto_ae.eventually
        (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [ht] with w hw
  let b := w.2
  have hp (b : ℝ) (q : QP) (he : b ∈ Set.Ioc (0 : ℝ) 1) : ‖City.brush b q‖ ≤ 1 := by
    obtain ⟨hb, ht⟩ := he
    unfold City.brush
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    apply mul_le_one₀ (pow_le_one₀ (by positivity) ht) (by positivity)
    apply (exp_le_one_iff).mpr
    exact neg_nonpos.mpr (mul_nonneg (sq_nonneg _) (Momentum.sq_nonnegative _))
  rw [Pill, mul_right_comm, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hp _ _ hw)
section integration
open intervalIntegral
variable (F : QP → ℝ) (hp : HeatPapers.Sheet F)

def tune (p : QP) (F : QP → ℝ) (r : ℝ) :=
  ∫ q, Pill r p q * F q ∂mplane

lemma owedK (p q : QP) (F : QP → ℝ) : Integrable (fun r => Pill r p q * F q) mint := by
  have ht : Continuous (fun r => Pill r p q * F q) := by
    unfold Pill City.brush
    fun_prop
  exact
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ 1 by norm_num)).mp
      (ht.intervalIntegrable ..)
include hp

lemma sameμ : (∫ q, (∫ r, Pill r p q * F q ∂mint) ∂mplane) = ∫ r, tune p F r ∂mint :=
  integral_integral_swap (bond p F hp)

lemma paymentμ (Y : ℝ → QP → ℂ) (c : ℂ) (hy : ∀ t q, Y t q = c * (Pill t p q * F q : ℝ)) :
    (∫ q, (∫ r in (0 : ℝ)..1, Y r q + Y r (-q)) ∂mplane) = 2 * c * ↑(∫ r in (0 : ℝ)..1, tune p F r) ∧
      Integrable (fun q => ∫ r in (0 : ℝ)..1, Y r q + Y r (-q)) mplane := by
  let Z (y : QP) := ∫ r, ((Pill r p y * F y : ℝ) : ℂ) ∂mint
  let W (y : QP) := ∫ r, Pill r p y * F y ∂mint
  have hx x : Z x = (W x : ℂ) := by
    unfold Z W
    rw [integral_complex_ofReal]
  have he (i : QP) : Integrable (fun r => c * ((Pill r p i * F i : ℝ) : ℂ)) mint :=
    (Complex.ofRealCLM.integrable_comp (owedK p i F)).const_mul _
  have ht (q : QP) : (∫ r in (0 : ℝ)..1, Y r q + Y r (-q)) = c * (Z q + Z (-q)) := by
    rw [integral_of_le zero_le_one]
    simp_rw [hy]
    rw [MeasureTheory.integral_add (he q) (he (-q)), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, mul_add]
  have hg : Integrable Z mplane := by
    rw [funext hx]
    exact
      Complex.ofRealCLM.integrable_comp
        (show Integrable W mplane from (bond p F hp).integral_prod_left)
  rw [funext ht]
  refine ⟨?_, (Integrable.const_mul (Integrable.add hg hg.comp_neg) _)⟩
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hg hg.comp_neg,
    integral_neg_eq_self]
  simp_rw [hx]
  rw [integral_complex_ofReal, sameμ p F hp, integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  ring
end integration
end YM.WilsonMS.BetaValue
