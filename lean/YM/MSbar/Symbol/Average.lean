import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Tactic

/-!
# Compact averages of symbols

Fixed masses. Allow *noncompact* parameter to cut supported coefficient, assuming a compact map
witness. For the unmasked Polch flow choose radial IR cutoff, use ordinary smoothness and polynomial
estimators. Does not assume estimates on perturbative outputs.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Symbol
open Function MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators Classical

universe u
variable {α : Type*} {E X Y R : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup R] [NormedSpace ℝ R] [MeasurableSpace α] {μ : Measure α}
  {K : Set Y} {f : X × Y → E}

-- Partial derivative tensor (unbundled)
def partialL (f : X × Y → E) (q : X × Y) := (fderiv ℝ f q).comp (ContinuousLinearMap.inl ℝ X Y)

omit [FiniteDimensional ℝ X] in
@[fun_prop] lemma partialL_smooth (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (partialL f) := by
  let B := (ContinuousLinearMap.compL ℝ X (X × Y) E).flip (ContinuousLinearMap.inl ℝ X Y)
  show ContDiff _ _ (B ∘ fderiv ℝ f)
  exact B.contDiff.comp (hf.fderiv_right (by simp))

omit [FiniteDimensional ℝ X] in
lemma partialL_fderiv (hf : ContDiff ℝ ∞ f) (x : X) (y : Y) : fderiv ℝ (fun w => f (w,y)) x = partialL f (x,y) :=by
  have he := ((hf.differentiable (by simp) (x,y)).hasFDerivAt).comp (f:=fun x=>(x,y)) x ((hasFDerivAt_id x).prodMk (hasFDerivAt_const _ _))
  exact he.fderiv

variable (B : R →L[ℝ] E →L[ℝ] E)
-- We need variant output space depends; use separate
variable {E' : Type u} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (b : R →L[ℝ] E →L[ℝ] E')
    {p : α → Y} (hp : AEStronglyMeasurable p μ) (hb : ∀ᵐ a ∂μ,p a ∈ K) (hc : IsCompact K)
    {w : α → R} (hw : Integrable w μ)
include hp hb hc hw
omit [FiniteDimensional ℝ X] [NormedSpace ℝ X] [NormedSpace ℝ Y] in
lemma average_integrable (hf : Continuous f) (x) : Integrable (fun a => b (w a) (f (x,p a))) μ:= by
  have hm := b.isBoundedBilinearMap.continuous
  have he : AEStronglyMeasurable (fun a=>f (x,p a)) μ := (hf.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hp
  obtain ⟨M,hM⟩:= hc.exists_bound_of_continuousOn (f:=fun y => f (x,y)) (hf.comp (continuous_const.prodMk continuous_id)).continuousOn
  refine ((hw.norm.const_mul ‖b‖).mul_const M).mono' (hm.comp_aestronglyMeasurable (hw.aestronglyMeasurable.prodMk he)) ?_
  filter_upwards [hb] with a h
  calc
    _ ≤ _ := b.le_opNorm₂ ..
    _ ≤ _ := by gcongr; exact hM _ h

lemma average_hasFDeriv (hf : ContDiff ℝ ∞ f) (x : X) :
    HasFDerivAt (fun x => ∫ a,b (w a) (f (x,p a)) ∂μ) (∫ a,(b (w a)).comp (partialL f (x,p a)) ∂μ) x := by
    let D := partialL f
    have hD := (partialL_smooth hf).continuous
    obtain ⟨M,hM⟩:= ((isCompact_closedBall x 1).prod hc).exists_bound_of_continuousOn hD.continuousOn
    have H : AEStronglyMeasurable (fun a => D (x,p a)) μ:= (hD.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hp
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (F':=fun x a=>(b (w a)).comp (D (x,p a))) (bound:=fun a=> ‖b‖*‖w a‖*M) (Metric.closedBall_mem_nhds x zero_lt_one)
    · exact Eventually.of_forall (fun x=> (average_integrable b hp hb hc hw hf.continuous x).aestronglyMeasurable)
    · exact average_integrable b hp hb hc hw hf.continuous x
    · exact (ContinuousLinearMap.compL ℝ X E E').isBoundedBilinearMap.continuous.comp_aestronglyMeasurable ((b.continuous.comp_aestronglyMeasurable hw.aestronglyMeasurable).prodMk H)
    · filter_upwards [hb] with a ha x' h'
      calc
        _ ≤ _ := ContinuousLinearMap.opNorm_comp_le ..
        _ ≤ _ := mul_le_mul (b.le_opNorm _) (hM (x',p a) ⟨h',ha⟩) (norm_nonneg _) (by positivity)
    · exact (hw.norm.const_mul _).mul_const _
    · refine Eventually.of_forall (fun a y _ => ?_)
      dsimp only [D]; rw [← partialL_fderiv hf]; exact (b (w a)).hasFDerivAt.comp y (((hf.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) y).hasFDerivAt)

omit hp hb hc hw [FiniteDimensional ℝ X] in
@[fun_prop] lemma tame_fderiv (hf : f.HasTemperateGrowth) : (fderiv ℝ f).HasTemperateGrowth := by
    refine ⟨hf.1.fderiv_right (by simp),fun n=>?_⟩
    simpa only [← norm_iteratedFDeriv_fderiv] using hf.2 (n+1)

omit hp hb hc hw [FiniteDimensional ℝ X] in
@[fun_prop] lemma partialL_growth (hf : f.HasTemperateGrowth) : (partialL f).HasTemperateGrowth := by
  let B := (ContinuousLinearMap.compL ℝ X (X × Y) E).flip (ContinuousLinearMap.inl ℝ X Y)
  show HasTemperateGrowth (B ∘ fderiv ℝ f)
  exact B.hasTemperateGrowth.comp (tame_fderiv hf)

lemma average_smooth (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun x => ∫ a,b (w a) (f (x,p a)) ∂μ):= by
   apply contDiff_infty.mpr; intro n
   induction n generalizing E E' with
   | zero =>
      refine contDiff_zero.mpr (Differentiable.continuous (𝕜:=ℝ) ?_)
      exact fun x => (average_hasFDeriv b hp hb hc hw hf x).differentiableAt
   | succ n ih =>
      rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_fderiv]
      have ht:= average_hasFDeriv b hp hb hc hw hf
      refine ⟨fun x=> (ht x).differentiableAt,by simp,?_⟩
      rw [funext fun x=> (ht x).fderiv]
      exact ih (b.precompR X) (partialL_smooth hf)

lemma average_growth (hf : f.HasTemperateGrowth) : HasTemperateGrowth (fun x => ∫ a,b (w a) (f (x,p a)) ∂μ):= by
  refine ⟨average_smooth b hp hb hc hw hf.1,?_⟩
  intro n; induction n generalizing E E' with
  | succ n ih =>
      simp_rw [← norm_iteratedFDeriv_fderiv]
      rw [funext fun x => (average_hasFDeriv b hp hb hc hw hf.1 x).fderiv]
      exact ih (b.precompR X) (partialL_growth hf)
  | zero =>
      simp only [norm_iteratedFDeriv_zero]
      obtain ⟨k,C,hC,h⟩ := hf.norm_iteratedFDeriv_le_uniform 0
      have he(y):‖f y‖≤ C*(1+‖y‖)^k := by simpa using h 0 le_rfl y
      obtain ⟨c,hc'⟩:= hc.exists_bound_of_continuousOn continuous_id.continuousOn
      replace hc' : ∀ᵐ a ∂μ, ‖p a‖ ≤ max c 0 := hb.mono fun a ha=>(hc' _ ha).trans (le_max_left ..)
      let d:=C*(1+max c 0)^k;let V (x:X):= (1+‖x‖)^k
      refine ⟨k,(∫ a,‖b‖*‖w a‖*d ∂μ),fun x=> ?_⟩
      rw [← integral_mul_const]
      refine norm_integral_le_of_norm_le (((hw.norm.const_mul _).mul_const d).mul_const _) ?_
      filter_upwards [hc'] with a h'
      calc
       _ ≤ _ := b.le_opNorm₂ ..
       _ ≤ ‖b‖*‖w a‖*(d*V x) := by
         apply mul_le_mul_of_nonneg_left (le_trans (he _) ?_) (by positivity); unfold d V; rw [mul_assoc,← mul_pow]; gcongr
         rw [Prod.norm_def]; rcases le_total ‖x‖ ‖p a‖ with H|H
         · rw [max_eq_right H]; exact (add_le_add_right h' _).trans (le_mul_of_one_le_right (by have h:=le_max_right c 0; positivity) (by simp))
         rw [max_eq_left H]; exact le_mul_of_one_le_left (by positivity) (by simp)
       _ = _ := (mul_assoc ..).symm

end YM.MSbar.Symbol
