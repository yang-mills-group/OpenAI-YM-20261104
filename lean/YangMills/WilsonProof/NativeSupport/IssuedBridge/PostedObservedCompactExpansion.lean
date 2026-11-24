import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedExamTreeSignedFields

/-! The original signed scalar estimate on all physical compact layouts pays
the public distributional target uniformly over its normalized test functions. -/
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.PostedObservedCompactExpansion
open Function Set Filter MeasureTheory YangMills YangMills.Matching
open scoped Topology BigOperators Classical Distributions

private theorem tested {n : ℕ} (φ : WilsonFamily.SeparatedTest n) (f : Points n → ℂ)
    (hf : ContinuousOn f (WilsonFamily.separated n)) : Integrable (fun x => φ x*f x) := by
  apply (integrableOn_iff_integrable_of_support_subset (s := tsupport φ) ?_).mp
  · exact (φ.continuous.continuousOn.mul (hf.mono φ.tsupport_subset)).integrableOn_compact φ.hasCompactSupport
  · intro x hx
    apply subset_tsupport φ
    exact fun h => hx (by simp [h])

theorem original {n : ℕ} (clock : ℝ → ℝ) (A : ℝ → Points n → ℂ) (P : ℕ → Points n → ℂ)
    (prescribed : ∀ k, ContinuousOn (P k) (WilsonFamily.separated n))
    (physical : ∀ᶠ s in 𝓝[>] 0, ContinuousOn (A s) (WilsonFamily.separated n))
    (paid : ∀ K : Set (Points n), IsCompact K → K ⊆ WilsonFamily.separated n →
      ∀ p : ℕ, ∀ ε > (0:ℝ), ∀ᶠ s in 𝓝[>] 0, ∀ x ∈ K,
        ‖A s x - ∑ k : Fin (p+1), (clock s : ℂ)^k.val*P k.val x‖ ≤ ε*|clock s|^p) :
    HasExpansion 0 clock A P := by
  refine ⟨fun φ k => tested φ _ (prescribed k),?_⟩
  intro K compact clear p ε eps
  let V := 1+volume.real K
  have positive : 0 < V := add_pos_of_pos_of_nonneg one_pos ENNReal.toReal_nonneg
  filter_upwards [paid K compact clear p (ε/V) (div_pos eps positive),physical] with s price source φ support norm
  have inc := tested φ _ source
  refine ⟨inc,?_⟩
  let R := fun x => φ x*(A s x-∑ k : Fin (p+1), (clock s : ℂ)^k.val*P k.val x)
  have term (k : Fin (p+1)) : Integrable (fun x => (clock s : ℂ)^k.val*(φ x*P k.val x)) :=
    (tested φ _ (prescribed k.val)).const_mul _
  have same : ∫ x, R x = (∫ x, φ x*A s x) - ∑ k : Fin (p+1), (clock s : ℂ)^k.val*∫ x, φ x*P k.val x := by
    have eqn (x) : R x = φ x*A s x - ∑ k : Fin (p+1), (clock s : ℂ)^k.val*(φ x*P k.val x) := by
      simp only [R,mul_sub,Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intros; ring
    simp_rw [eqn]
    rw [integral_sub inc (integrable_finsetSum _ fun k _ => term k),integral_finsetSum _ fun k _ => term k]
    simp_rw [integral_const_mul]
  rw [←same,←setIntegral_eq_integral_of_forall_compl_eq_zero (s:=K) (f:=R)
    (fun x hx => by simp [R,image_eq_zero_of_notMem_tsupport (fun z => hx (support z))])]
  have bound (x) (hx : x ∈ K) : ‖R x‖ ≤ ε/V*|clock s|^p := by
    have test : ‖φ x‖ ≤ 1 := by simpa only [norm_iteratedFDeriv_zero] using norm 0 le_rfl x hx
    exact (norm_mul _ _).trans_le ((mul_le_mul test (price x hx) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  calc
    _ ≤ (ε/V*|clock s|^p)*volume.real K := norm_setIntegral_le_of_norm_le_const compact.measure_lt_top bound
    _ ≤ (ε/V*|clock s|^p)*V := mul_le_mul_of_nonneg_left (by simp [V]) (by positivity)
    _ = ε*|clock s|^p := by field_simp

end IssuedBridge.PostedObservedCompactExpansion
