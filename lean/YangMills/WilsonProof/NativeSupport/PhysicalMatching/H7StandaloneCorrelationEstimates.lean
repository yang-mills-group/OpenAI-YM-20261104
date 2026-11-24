import YangMills.WilsonProof.NativeSupport.MeasuredShapeJets

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YangMills.Matching.CorrelationOnly
open Filter Set MeasureTheory
open scoped Topology BigOperators Classical

theorem shapeValue {n j : ℕ} {f h : Points n → ℂ} {x : Points n} {bound : ℝ}
    (H : shapeJetEstimateAt j f h x bound) : ‖f x - h x‖ ≤ bound := by
  simpa only [norm_iteratedFDeriv_zero] using H.2.2 0 (Nat.zero_le j)

theorem compactOfShapeJets {g : GaugeGroup} {B : Maxwell.Reference g}
    {C : WilsonFamily g} {T : Hierarchy C} {n p : ℕ} (d : Fin n → ℕ)
    (clock : ℝ → ℝ) (K : Set (Points n)) (o : Spacetime)
    (actual : Option T.Character → ((i : Fin n) → B.sector (d i)) → Spacetime → ℝ → Points n → ℂ)
    (predicted : ((i : Fin n) → B.sector (d i)) → ℝ → Points n → ℂ)
    (jets : ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ phase v center x, x ∈ K →
      shapeJetEstimateAt 0 (actual phase v center s) (predicted v s) x
        (A * (∏ i, sectorMass (v i)) * |clock s| ^ (p+1))) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ phase v x, x ∈ K →
      ‖actual phase v o s x - predicted v s x‖ ≤
        A * (∏ i, sectorMass (v i)) * |clock s| ^ (p+1) := by
  obtain ⟨A, hA, h⟩ := jets
  exact ⟨A, hA, h.mono fun s hs phase v x hx => shapeValue (hs phase v o x hx)⟩

theorem testedCompactRemainder {n : ℕ} (K : Set (Points n)) (hK : IsCompact K)
    (φ : WilsonFamily.SeparatedTest n) (hs : tsupport φ ⊆ K)
    (f h : Points n → ℂ) (bound : ℝ)
    (hφ : ∀ x ∈ K, ‖iteratedFDeriv ℝ 0 (fun y : Points n => φ y) x‖ ≤ 1)
    (hd : ∀ x ∈ K, ‖f x - h x‖ ≤ bound) :
    ‖∫ x, φ x * (f x - h x)‖ ≤ bound * volume.real K := by
  let w := fun x : Points n => φ x * (f x - h x)
  have outside (x : Points n) (hx : x ∉ K) : w x = 0 := by
    have hz : φ x = 0 := by
      by_contra hn
      exact hx (hs (subset_closure (show x ∈ Function.support (fun y : Points n => φ y) from hn)))
    simp [w, hz]
  have restrict : w = K.indicator w := by
    funext x
    by_cases hx : x ∈ K
    · simp [hx]
    · simp [hx, outside x hx]
  change ‖∫ x, w x‖ ≤ _
  conv_lhs => rw [restrict, integral_indicator hK.measurableSet]
  apply norm_setIntegral_le_of_norm_le_const hK.measure_lt_top
  intro x hx
  have h₀ : ‖φ x‖ ≤ 1 := by simpa only [norm_iteratedFDeriv_zero] using hφ x hx
  calc ‖w x‖ = ‖φ x‖ * ‖f x - h x‖ := norm_mul _ _
    _ ≤ 1 * ‖f x - h x‖ := mul_le_mul_of_nonneg_right h₀ (norm_nonneg _)
    _ ≤ bound := by simpa only [one_mul] using hd x hx

end YangMills.Matching.CorrelationOnly

