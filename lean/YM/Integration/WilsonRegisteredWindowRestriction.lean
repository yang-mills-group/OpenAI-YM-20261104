import YM.Integration.ActualTrajectoryTransport
import YM.OPE.Therm.Law
import YM.RGComparison.Core16.Spool.Beacon
import Mathlib.MeasureTheory.Measure.Real

/-! The loss from local exceptions in a signed, finite Wilson stencil sum.
Each summand uses only its own occupied collars. Its true conditional word and
its original complex coefficient are kept until the absolute error is priced. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredWindowRestriction
open Filter MeasureTheory Lattice Wilson RG RGComparison.Core16.Spool OPE.Therm
open scoped BigOperators Classical
variable {G : Gauge} {ι : Type} [Fintype ι]

def wordBound (J : ι → Lamp G) : ℝ := 2 * (encouraging J).choose

theorem word {f : Side} (J : ι → Lamp G) (o : ι → Site f) (U : Config G f) :
    ‖tally J o U‖ ≤ wordBound J := by
  let x := U ∘ legs J o
  have h := (encouraging J).choose_spec.2
  rw [← exhibition J o U]
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  have re : |(exhibit J x).re| ≤ (encouraging J).choose := by
    simpa only [look, Bool.false_eq_true, ↓reduceIte, Complex.reCLM_apply, Real.norm_eq_abs]
      using h false x
  have im : |(exhibit J x).im| ≤ (encouraging J).choose := by
    simpa only [look, ↓reduceIte, Complex.imCLM_apply, Real.norm_eq_abs] using h true x
  change |(exhibit J x).re| + |(exhibit J x).im| ≤ 2 * (encouraging J).choose
  linarith only [re, im]

/-- The expectation of the absolute signed exception uses the actual Wilson
marginal. The finite collar count is per summand and the word tariff is uniform
in volume, cutoff and all stencil translations. -/
theorem bank (C : Family G) (hC : C.Makes) {N per k j : ℕ} (top : j ≤ N) (low : k ≤ j)
    {A I : Type} [Fintype A] [Fintype I] (J : A → ι → Lamp G)
    (o : A → ι → Site (C.side j per)) (w : A → ℂ)
    (E : A → I → Set (Config G (C.side k per))) (me : ∀ a i, MeasurableSet (E a i))
    (τ : ℝ) (paid : ∀ a i, (scene C.path N per k).real (E a i) ≤ τ) :
    ∫ V, ‖∑ a, (⋃ i, E a i).indicator
      (fun U => w a * actualTransport C (N := N) (tally (J a) (o a)) low U) V‖
      ∂scene C.path N per k ≤ ((Fintype.card I : ℝ) * τ) * ∑ a, ‖w a‖ * wordBound (J a) := by
  let μ := scene C.path N per k
  letI : IsProbabilityMeasure μ := probability hC.wilson (low.trans top)
  let Q (a : A) := ⋃ i, E a i
  let F (a : A) := actualTransport C (N := N) (tally (J a) (o a)) low
  let B (a : A) := ‖w a‖ * wordBound (J a)
  let X (a : A) := (Q a).indicator (fun U => w a * F a U)
  let Y (a : A) := (Q a).indicator (fun _ => B a)
  have qm (a : A) : MeasurableSet (Q a) := MeasurableSet.iUnion (me a)
  have bound (a : A) (V) : ‖F a V‖ ≤ wordBound (J a) :=
    actualTransport_norm_le C hC top (word (J a) (o a)) low V
  have xf (a : A) : Integrable (X a) μ := by
    have priorTrace := actualTransport_integrable C hC top
      (tally_cont (J a) (o a)).aestronglyMeasurable (word (J a) (o a)) low
    have mv : AEStronglyMeasurable (F a) μ :=
      AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _) priorTrace.aestronglyMeasurable
    have fv := Integrable.of_bound mv (wordBound (J a)) (ae_of_all _ (bound a))
    exact (fv.const_mul (w a)).indicator (qm a)
  have yf (a : A) : Integrable (Y a) μ := (integrable_const (B a)).indicator (qm a)
  have dom (V) : ‖∑ a, X a V‖ ≤ ∑ a, Y a V := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a _
    by_cases h : V ∈ Q a
    · simp only [X, Y, Set.indicator_of_mem h, norm_mul]
      exact mul_le_mul_of_nonneg_left (bound a V) (norm_nonneg _)
    · simp [X, Y, h]
  have prob (a : A) : μ.real (Q a) ≤ (Fintype.card I : ℝ) * τ := by
    apply (measureReal_iUnion_fintype_le (μ := μ) (E a)).trans
    apply (Finset.sum_le_sum (g := fun _ => τ) (fun i _ => paid a i)).trans_eq
    simp [nsmul_eq_mul]
  change (∫ V, ‖∑ a, X a V‖ ∂μ) ≤ _ * ∑ a, B a
  calc
    _ ≤ ∫ V, ∑ a, Y a V ∂μ := integral_mono
      (integrable_finsetSum Finset.univ (fun a _ => xf a)).norm
      (integrable_finsetSum Finset.univ (fun a _ => yf a)) dom
    _ = ∑ a, μ.real (Q a) * B a := by
      rw [integral_finsetSum Finset.univ (fun a _ => yf a)]
      apply Finset.sum_congr rfl
      intro a _
      rw [show Y a = (Q a).indicator (fun _ => B a) from rfl,
        integral_indicator (qm a), setIntegral_const, smul_eq_mul]
    _ ≤ ∑ a, ((Fintype.card I : ℝ) * τ) * B a := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_right (prob a)
        (mul_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) (encouraging (J a)).choose_spec.1))
    _ = _ := (Finset.mul_sum ..).symm

end YM.Integration.WilsonRegisteredWindowRestriction
