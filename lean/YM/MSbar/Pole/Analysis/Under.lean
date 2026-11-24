import YM.MSbar.Pole.Analysis.Syntax
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Differentiating dimensional integrations

Capacity in the integrated variable, no continuity in that variable needed.
Some of the finite dimensional `Window` argument in `Further/DENSE_MIXED_KERNELS`
is specialized here (now we need mixed growth seminorms, and permit a.e.).
-/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory
open scoped ContDiff Topology Classical BigOperators Interval

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Z : Type*} [MeasurableSpace Z]

/-- `τ` includes any holomorphic probe coordinates regarded as real ones. -/
structure Barrel (μ : Measure Z) (τ : Set E) (p q : Price E) (f : Z → E → F) : Prop where
  roomy : IsOpen τ
  scale : ContinuousOn p.val τ
  ambient : ∀ᵐ u ∂μ, ∀ x∈τ, ContDiffAt ℝ ∞ (f u) x
  measurable : ∀ x∈τ, AEStronglyMeasurable (fun i => f i x) μ
  receipt : ∀ i k : ℕ, ∃ (b : Z → ℝ) (l : ℕ), (∀ᵐ u ∂μ, 0 ≤ b u) ∧ Integrable b μ ∧
     ∀ᵐ u ∂μ, ∀ x∈τ, ‖iteratedFDeriv ℝ i (f u) x‖ * q x^k ≤ b u * p x ^ l

variable {μ : Measure Z} {τ : Set E} {p q : Price E} {f : Z → E → F}
namespace Barrel
omit [FiniteDimensional ℝ E] in
lemma integrable (h : Barrel μ τ p q f) {x : E} (hx : x∈τ) : Integrable (fun i => f i x) μ := by
  obtain ⟨b,l,-,hb,H⟩ := h.receipt 0 0
  refine (hb.mul_const (p x^l)).mono' (h.measurable _ hx) (H.mono fun u hu => ?_); simpa using hu x hx

lemma derives (h : Barrel μ τ p q f) : Barrel μ τ p q (fun u => fderiv ℝ (f u)) := by
  refine ⟨h.roomy,h.scale,h.ambient.mono (fun i hi x hx => (hi x hx).fderiv_right (by simp)),fun x hx => ?_, fun i k => ?_⟩
  · have he (v : E) : AEStronglyMeasurable (fun i => fderiv ℝ (f i) x v) μ := by
      let T (r : ℝ) (i : Z) := if x+r • v∈τ then r⁻¹ • (f i (x+r • v)-f i x) else 0
      have ht r : AEStronglyMeasurable (T r) μ := by
        unfold T; split_ifs with hm
        · exact ((h.measurable _ hm).sub (h.measurable _ hx)).const_smul _
        exact aestronglyMeasurable_zero
      apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] 0) ht
      have H : Tendsto (fun r : ℝ => x+r • v) (𝓝 0) (𝓝 x) := by
        simpa only [zero_smul,add_zero] using (show Continuous (fun r : ℝ=>x+r • v) from by fun_prop).tendsto 0
      filter_upwards [h.ambient] with i hi
      refine (((hi x hx).differentiableAt (by simp)).hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero.congr' ?_
      filter_upwards [H.mono_left nhdsWithin_le_nhds |>.eventually (h.roomy.mem_nhds hx)] with r hr using (eq_comm.mp (if_pos hr))
    let B := Module.finBasis ℝ E
    let R (j) := ContinuousLinearMap.smulRightL ℝ E F (LinearMap.toContinuousLinearMap (B.coord j))
    have hm (j) : AEStronglyMeasurable (fun i => R j (fderiv ℝ (f i) x (B j))) μ :=
      (R j).continuous.comp_aestronglyMeasurable (he (B j))
    refine (Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => hm i)).congr (Eventually.of_forall fun i => ?_)
    apply ContinuousLinearMap.ext; intro v
    rw [Finset.sum_apply,_root_.sum_apply]
    change (∑ j, B.repr v j • fderiv ℝ (f i) x (B j)) = _
    simp only [← map_smul,← map_sum,B.sum_repr]
  obtain ⟨b,l,hb,H,hv⟩ := h.receipt (i+1) k
  exact ⟨b,l,hb,H,hv.mono fun u hu x hx => by simpa only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, LinearIsometryEquiv.norm_map] using hu x hx⟩

lemma exchange (h : Barrel μ τ p q f) {x : E} (hx : x∈τ) :
    HasFDerivAt (fun z => ∫ u, f u z ∂μ) (∫ u, fderiv ℝ (f u) x ∂μ) x := by
  obtain ⟨b,l,hb,H,hv⟩ := h.derives.receipt 0 0
  let K := p x+1
  let S := {z∈τ|p z≤K}
  have hs : S ∈ 𝓝 x := inter_mem (h.roomy.mem_nhds hx)
    ((h.scale.continuousAt (h.roomy.mem_nhds hx)) (ge_mem_nhds (lt_add_one _)))
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F':=fun y i => fderiv ℝ (f i) y) (bound:=fun u => b u*K^l) hs
    (mem_of_superset (h.roomy.mem_nhds hx) (fun z hz => h.measurable z hz)) (h.integrable hx) (h.derives.measurable _ hx) ?_ (H.mul_const _) ?_
  · filter_upwards [hv,hb] with u hu hp z hz
    exact (show ‖fderiv ℝ (f u) z‖ ≤ b u * p z^l by simpa using hu z hz.1).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (p.pos _).le hz.2 l) hp)
  exact h.ambient.mono fun u hu z hz => ((hu z hz.1).differentiableAt (by simp)).hasFDerivAt

lemma through (h : Barrel μ τ p q f) (n : ℕ) {x} (hx : x∈τ) : ContDiffAt ℝ n (fun z => ∫ u, f u z ∂μ) x := by
  induction n generalizing F with
  | zero =>
    refine (contDiffOn_zero.mpr (fun y hy => (h.exchange hy).continuousAt.continuousWithinAt)).contDiffAt (h.roomy.mem_nhds hx)
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiffAt_succ_iff_hasFDerivAt]
    refine ⟨fun z => ∫ u, fderiv ℝ (f u) z ∂μ, ⟨τ,h.roomy.mem_nhds hx,fun _ hy => h.exchange hy⟩, ih h.derives⟩

lemma all_orders [CompleteSpace F] (h : Barrel μ τ p q f) (n : ℕ) {x} (hx : x∈τ) :
    Integrable (fun u => iteratedFDeriv ℝ n (f u) x) μ ∧
    iteratedFDeriv ℝ n (fun z => ∫ u, f u z ∂μ) x = ∫ u, iteratedFDeriv ℝ n (f u) x ∂μ := by
  induction n generalizing F with
  | zero =>
    simp_rw [iteratedFDeriv_zero_eq_comp]
    let B := (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
    exact ⟨B.integrable_comp (h.integrable hx),(B.integral_comp_comm (h.integrable hx)).symm⟩
  | succ n ih =>
    obtain ⟨hm,hh⟩ := ih h.derives

    let B := (continuousMultilinearCurryRightEquiv' ℝ n E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have he : fderiv ℝ (fun z => ∫ u, f u z ∂μ) =ᶠ[𝓝 x] fun z => ∫ u, fderiv ℝ (f u) z ∂μ :=
      mem_of_superset (h.roomy.mem_nhds hx) (fun y hy => (h.exchange hy).fderiv)
    constructor
    · simp_rw [iteratedFDeriv_succ_eq_comp_right, comp_apply]
      refine (show Integrable (fun u => B (iteratedFDeriv ℝ n (_root_.fderiv ℝ (f u)) x)) μ from ?_)
      have hQ := B.integrable_comp hm
      exact hQ
    simp_rw [iteratedFDeriv_succ_eq_comp_right, comp_apply]
    rw [(he.iteratedFDeriv (𝕜:=ℝ) n).eq_of_nhds,hh]
    have hQ := B.integral_comp_comm hm
    exact hQ.symm

lemma integrates [CompleteSpace F] (h : Barrel μ τ p q f) : Packet τ p q (fun z => ∫ u, f u z ∂μ) := by
  refine ⟨fun x hx => contDiffAt_infty.mpr (fun n => h.through n hx),fun n k => ?_⟩
  obtain ⟨b,l,hb,H,hv⟩ := h.receipt n k
  refine ⟨∫ u,b u ∂μ,l,integral_nonneg_of_ae hb,fun x hx => ?_⟩
  obtain ⟨hm,hh⟩ := h.all_orders n hx
  rw [hh]
  refine (mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm (μ:=μ) _) (pow_nonneg (q.pos _).le _)).trans ?_
  rw [← integral_mul_const,← integral_mul_const]
  exact integral_mono_ae (hm.norm.mul_const _) (H.mul_const _) (hv.mono fun u hu => hu x hx)
end Barrel
end YM.MSbar.Pole
