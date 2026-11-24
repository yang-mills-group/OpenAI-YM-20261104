import YM.RGComparison.Core16.Offset

/-!
# Pay offset and grade costs for rescaled output

Export for ALL positive `a`. This does not assert after-volume/depth constants are affordable on
the schedule, but avoids a premise that the *value* of actual `g_N` belongs to some dramatically
shrinking, maybe-unaffordable finite-volume Taylor domain.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Descent
open Lattice RG Tree Wilson Precision Push.BetaTransport
open Function Filter MeasureTheory Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open PertExtension PertExtension.Series Tested Radial
variable {G : Gauge} {n c : Side} {d : Descent n c}

section large
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : Config G n → X} {g : Config G n → ℝ} (h : d.OK G) (β : ℕ → ℝ)

include h
lemma output_domination (hf : Integrable F (prior G n)) (hg : Integrable g (prior G n))
    (H : ∀ x, ‖F x‖ ≤ g x) (x : Config G c) : ‖d.output β F x‖ ≤ d.output β g x := by
  induction d generalizing β with
  | nil => simpa using H x
  | push S T d ih =>
    rw [output_push,output_push]; unfold StepData.push
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono (StepData.push_slice (S.isKernel h.1 (β 1)) x _
      (output_integrable h.2 _ hf)|>.norm) (StepData.push_slice (S.isKernel h.1 (β 1)) _ _
      (output_integrable h.2 _ hg)) ?_
    intro i; dsimp only; rw [norm_smul, Real.norm_of_nonneg (S.density_positive ..), smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (ih h.2 _ _) (S.density_positive ..)

lemma conditioned_bound {C : ℝ} (hc : ∀ x, ‖F x‖ ≤ C) (hi : Continuous F) (x : Config G c) :
    ‖d.conditioned β F x‖ ≤ C := by
  let f : Config G n → ℝ := bare (β d.depth)
  have H : ‖d.weighted β F x‖ ≤ C * d.vacuum β x := by
    refine (output_domination (F := f • F) (g := C • f) h β
      (((bare_cont _).smul hi).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((bare_integrable _).const_mul _) ?_ x).trans_eq ?_
    · intro y; rw [Pi.smul_apply', norm_smul,Real.norm_of_nonneg (show 0 ≤ f y from (bare_pos ..).le),
        Pi.smul_apply, smul_eq_mul, mul_comm C]; exact mul_le_mul_of_nonneg_left (hc y) (bare_pos ..).le
    rw [output_smul_real_const]; rfl
  unfold conditioned; rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr (positive β h x)).le, mul_comm, ← div_eq_mul_inv]
  exact (div_le_iff₀ (positive β h x)).mpr H
end large

/-- Separate rough bill outside the germ (coefficient costs from the independent polynomial
visible; large couplings deliberately included for finite-cutoff stress tests). -/
private lemma rough_price (r w : ℕ) {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (f : Config G n → X) (u : ℕ → X) (h : d.OK G)
    (hf : Continuous f) {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a, s≤a → ∀ β : ℕ → ℝ,
      ‖(a⁻¹)^w • d.conditioned β f 1 - peval u r a‖ ≤ C*a^(r+1) := by
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  let k : ℕ → ℝ := fun i => (s⁻¹)^(r+1-i)*‖u i‖
  let b := s⁻¹^w * |M|
  have hb : 0 ≤ b := by unfold b; positivity
  have hh (i) : 0 ≤ k i := by unfold k; positivity
  let q := ∑ i ∈ Finset.range (r+1), k i
  have he : 0 ≤ q := Finset.sum_nonneg fun i _ => hh i
  refine ⟨b/s^(r+1) + q,by positivity,fun a ha β => ?_⟩
  have hx := hs.trans_le ha
  have hw (i : ℕ) (hi : i ≤ r) : a^i ≤ a^(r+1)*(s⁻¹)^(r+1-i) := by
    apply le_of_mul_le_mul_right (a:=s^(r+1-i)) ?_ (pow_pos hs _)
    rw [mul_assoc, inv_pow,inv_mul_cancel₀ (pow_pos hs _).ne',mul_one]
    exact (mul_le_mul_of_nonneg_left (by gcongr) (pow_pos hx i).le).trans_eq
      ((pow_add a i (r+1-i)).symm.trans (by rw [show i+(r+1-i)=_ from (by omega : i+(r+1-i)=r+1)])) -- simplify equality
  have hf' : ‖peval u r a‖ ≤ q*a^(r+1) := by
    unfold peval Zone.eval; unfold q; rw [Finset.sum_mul]
    refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i hi => ?_)
    dsimp only; rw [norm_smul, Real.norm_of_nonneg (pow_pos hx i).le]
    exact (mul_le_mul_of_nonneg_right (hw i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (norm_nonneg _)).trans_eq (by unfold k; ring)
  have hl : ‖a⁻¹ ^ w • d.conditioned β f 1‖ ≤ b/s^(r+1)*a^(r+1) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ a⁻¹ ^ w)]
    have hfN : ‖d.conditioned β f 1‖ ≤ |M| := conditioned_bound h β (fun i => (hM i (Set.mem_univ _)).trans (le_abs_self _)) hf _
    apply le_trans (b:=b)
    · unfold b; gcongr
    grw [← ha] -- replaces s? decreases numerator? goal b ≤ b / s^... * a..., yes
    rw [div_mul_cancel₀ _ (pow_pos hs _).ne']
  apply (norm_sub_le ..).trans ((add_le_add hl hf').trans_eq (add_mul ..).symm)

section consumer
variable (P : ChartRatio G) (R : LocalRatio P) (r : ℕ) {M : ℝ} {v : ℕ → ℝ} {w : ℕ}
    (h : d.Room G) {F : Config G n → ℝ} (hf : d.Testable F) (hG : d.grade F w)
    (gV : d.Band M v)
include R h hf hG gV
/-- Through EVERY fixed order. Note extra term pays the actual distance to the prescribed shifts,
with credit of two powers. For independent local coefficients through order r=1 we can ignore the
shifts (`v=0`, but `u i = β_i - a⁻²` always on the actual side).

Uniform over all positive `a` at one fixed finite history, not uniformly for rising `N` or increasing
period. In particular constants dependent on **this** integral's dimension, Geometry, all patch,
tag, marking data etc., no uniform smallness after their growth.
-/
theorem covers : ∃ A E : ℝ, 0 ≤ A ∧ 0 ≤ E ∧ ∀ a : ℝ, 0 < a → ∀ (u : ℕ → ℝ) (δ : ℝ),
    d.Band M u → d.Band δ (u-v) →
      ‖a⁻¹^w * d.conditioned (offset u a) F 1 - peval (fun j => ranking P d v F (w+j)) r a‖ ≤
        A*a^(r+1) + E*a^2*δ := by
  obtain ⟨X,hX,hc⟩ := conditioned_offset_grade F P R h hf hG gV
  obtain ⟨Y,hY,he⟩ := rescaled_formula P R h v hf hG r
  have hh := he.and hc; rw [eventually_nhdsWithin_iff] at hh; obtain ⟨s,hs,hS⟩ := Metric.mem_nhds_iff.mp hh
  obtain ⟨C,hC,H⟩ := rough_price r w F (fun j => ranking P d v F (w+j)) (room_ok d h) hf.neat hs
  refine ⟨Y+C,X,add_nonneg hY hC,hX,fun a ha u δ hu hδ => ?_⟩
  by_cases hl : a<s
  · have hz : a ∈ Metric.ball (0:ℝ) s := by simpa [abs_of_pos ha] using hl
    obtain ⟨h₁,h₂⟩ := hS hz (show 0<a from ha)
    let f (u) := d.conditioned (offset u a) F 1
    let r' := peval (fun j => ranking P d v F (w+j)) r a
    change ‖_*f u - r'‖ ≤ _
    rw [show a⁻¹^w*f u-r'=a⁻¹^w*f v-r'+a⁻¹^w*(f u-f v) by ring]; apply (norm_add_le ..).trans
    rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ a⁻¹ ^ w)]
    refine add_le_add (le_trans (b:=Y*a^(r+1)) h₁ (by gcongr; linarith))
      ((mul_le_mul_of_nonneg_left (h₂ u δ hu hδ) (by positivity : 0 ≤ a⁻¹^w)).trans_eq ?_)
    · rw [pow_add, inv_pow]; field_simp
  have hδ' := nonnegativeBand hδ
  apply le_trans (b:=C*a^(r+1)) (H a (le_of_not_gt hl) (offset u a))
  calc
    _ ≤ (Y+C)*a^(r+1) := by gcongr; linarith
    _ ≤ _ := le_add_of_nonneg_right (by positivity)
end consumer
end YM.RGComparison.Core16.Descent
