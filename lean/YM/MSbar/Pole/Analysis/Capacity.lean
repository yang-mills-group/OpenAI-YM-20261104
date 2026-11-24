import YM.MSbar.Pole.Analysis.Under
import Mathlib.Analysis.Complex.Conformal

/-! Joint (real and complex-parameter) mixed-domain symbols, integrated over slices. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory
open scoped ContDiff Topology Classical BigOperators
variable {E A F : Type} [NormedAddCommGroup E] [NormedAddCommGroup A] [NormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℝ A]
  {Z : Type*} [MeasurableSpace Z]

section holo
-- f z probes the first complex coordinate; useful also for artificial exponents in DR
lemma holo [FiniteDimensional ℝ E] {μ : Measure Z} {f : Z → (ℂ × E) → ℂ}
    {U : Set (ℂ×E)} {p q : Price (ℂ×E)} (h : Barrel μ U p q f) {z : ℂ} {x : E}
    (hz : (z,x) ∈ U) (hf : ∀ᵐ u ∂μ, DifferentiableAt ℂ (fun y => f u (y,x)) z) :
    DifferentiableAt ℂ (fun y => ∫ u, f u (y,x) ∂μ) z := by
  let J := (ContinuousLinearMap.inl ℝ ℂ E)
  have hj : HasFDerivAt (fun y => (y,x)) J z := (hasFDerivAt_id (𝕜:=ℝ) z).prodMk (hasFDerivAt_const ..)
  have he := (h.exchange hz).comp z hj
  let B (u : Z) := fderiv ℝ (f u) (z,x)
  refine differentiableAt_complex_iff_differentiableAt_real.mpr ⟨he.differentiableAt,?_⟩
  rw [show fderiv ℝ (fun y => ∫ u, f u (y,x) ∂μ) z = (∫ u, B u ∂μ).comp J from he.fderiv]
  have hm : Integrable B μ := h.derives.integrable hz
  simp_rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.integral_apply hm,← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [hf,h.ambient] with u hu h'
  have hl := (differentiableAt_complex_iff_differentiableAt_real.mp hu).2
  rw [show fderiv ℝ (fun y => f u (y,x)) z=(B u).comp J from ((((h' (z,x) hz).differentiableAt (by simp)).hasFDerivAt.comp z hj).fderiv)] at hl
  exact hl
end holo
section slice
variable [NormedSpace ℝ F] {φ : A→F} {f : E→F}
lemma iter_affine (L : E→L[ℝ] A) (b : A) (x : E) (i : ℕ) (h : ContDiffAt ℝ i φ (b+L x)) :
    iteratedFDeriv ℝ i (fun y=>φ (b+L y)) x=(iteratedFDeriv ℝ i φ (b+L x)).compContinuousLinearMap fun _=>L := by
  let g (y:A):=φ (b+y); change iteratedFDeriv ℝ i (g ∘ L) x = _
  rw [← iteratedFDeriv_comp_add_left (f:=φ)] -- maybe syntax
  have hb : ContDiffAt ℝ i g (L x) := h.comp _ (contDiffAt_const.add contDiffAt_id)
  obtain ⟨t,ht,ho,hm⟩ := mem_nhds_iff.mp (hb.eventually (by simp))
  have h₁ := L.iteratedFDerivWithin_comp_right (ho.contDiffOn_iff.mpr fun _ hy => (ht hy)) ho.uniqueDiffOn (ho.preimage L.continuous).uniqueDiffOn hm (n:=↑i) (i:=i) (by exact le_rfl)
  rw [iteratedFDerivWithin_of_isOpen _ ho hm,iteratedFDerivWithin_of_isOpen _ (ho.preimage L.continuous) (mem_preimage.mpr hm)] at h₁
  exact h₁

lemma iter_affine_le (L : E→L[ℝ] A) (b : A) (x : E) (i : ℕ) (h : ContDiffAt ℝ i φ (b+L x)) :
    ‖iteratedFDeriv ℝ i (fun y=>φ (b+L y)) x‖≤‖iteratedFDeriv ℝ i φ (b+L x)‖*‖L‖^i := by
  rw [iter_affine L b x i h]; simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le (iteratedFDeriv ℝ i φ (b+L x)) (fun _ : Fin i => L)

lemma iter_right_le {φ : A × E → F} {z : A} {x : E} {i : ℕ} (h : ContDiffAt ℝ i φ (z,x)) :
    ‖iteratedFDeriv ℝ i (fun y => φ (z,y)) x‖ ≤ ‖iteratedFDeriv ℝ i φ (z,x)‖ * ‖ContinuousLinearMap.inr ℝ A E‖ ^ i := by
  have hb := iter_affine_le (φ:=φ) (ContinuousLinearMap.inr ℝ A E) (z,0) x i (by simpa using h)
  simpa using hb
variable {μ : Measure Z} {G : Z → E → F}
  {U : Set E} {T : Set A} {p q : Price E}
/- construct a capacity from joint seminorms. -/
lemma fullSlice {φ : A × E → F} (o : IsOpen U) (c : ContinuousOn p.val U) (a : Z → A) (j : Price A) (ha : ∀ᵐ z ∂μ, a z∈T)
    (hp : Packet (T×ˢ U) (p.back Prod.snd) (j.back Prod.fst * q.back Prod.snd) φ)
    (hm : ∀ x∈U, AEStronglyMeasurable (fun z => φ (a z,x)) μ)
    (M : ℕ) (hi : Integrable (fun z => (j (a z) ^ M)⁻¹) μ) :
    Barrel μ U p q (fun z x => φ (a z,x)) := by
  refine ⟨o,c,ha.mono (fun z hv x hx => (hp.smooth (a z,x) ⟨hv,hx⟩).comp x (contDiffAt_const.prodMk contDiffAt_id)),hm,fun i k => ?_⟩
  obtain ⟨C,e,hc,H⟩ := hp.budget i (max k M)
  let w := ‖ContinuousLinearMap.inr ℝ A E‖ ^ i
  have hw : 0 ≤ w := by unfold w; positivity
  refine ⟨fun z => (j (a z) ^ M)⁻¹ * (C*w),e,Eventually.of_forall (fun z => mul_nonneg (inv_nonneg.mpr (pow_nonneg (j.pos _).le _)) (mul_nonneg hc hw)),hi.mul_const _,?_⟩
  filter_upwards [ha] with z hz x hx
  have hf : ‖iteratedFDeriv ℝ i (fun y => φ (a z,y)) x‖ ≤ ‖iteratedFDeriv ℝ i φ (a z,x)‖*w := iter_right_le (hp.localn i (mem_prod.mpr ⟨hz,hx⟩))
  have hy := H (a z,x) ⟨hz,hx⟩
  change ‖iteratedFDeriv ℝ i φ (a z,x)‖ * (j (a z)*q x)^ max k M ≤ C*p x^e at hy
  rw [mul_comm _ (C*w),mul_right_comm]; change _ ≤ _ * _⁻¹; rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (j.pos _) _)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ i φ (a z,x)‖*w *q x^k * j (a z)^M := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf (pow_nonneg (q.pos _).le _)) (pow_nonneg (j.pos _).le _)

    _ = (‖iteratedFDeriv ℝ i φ (a z,x)‖*(j (a z)^M * q x^k))*w := by ring
    _ ≤ (C*p x^e)*w := by
      refine mul_le_mul_of_nonneg_right (le_trans ?_ hy) hw; rw [mul_pow]; exact mul_le_mul_of_nonneg_left
        (mul_le_mul (j.snap _ (le_max_right k M)) (q.snap _ (le_max_left ..)) (pow_nonneg (q.pos _).le _) (pow_nonneg (j.pos _).le _)) (norm_nonneg _)
    _ = _ := by ring
end slice
end YM.MSbar.Pole
