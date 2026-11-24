import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneCorrelationEstimates

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YangMills.Matching.CorrelationOnly
open Filter Set MeasureTheory
open scoped Topology BigOperators Classical

def crop {n : ℕ} (clock : ℝ → ℝ) (predicted : ℕ → Points n → ℂ)
    (N : ℕ) (s : ℝ) (x : Points n) : ℂ :=
  ∑ k : Fin (N+1), (clock s : ℂ)^k.val * predicted k.val x

def CompactShapeCrops {n : ℕ} (clock : ℝ → ℝ) (actual : ℝ → Points n → ℂ)
    (predicted : ℕ → Points n → ℂ) : Prop :=
  ∀ (p : ℕ) (K : Set (Points n)), IsCompact K → K ⊆ WilsonFamily.separated n →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ x ∈ K,
      shapeJetEstimateAt 0 (actual s) (crop clock predicted p s) x
        (A * |clock s|^(p+1))

private theorem nextCrop {n : ℕ} (clock : ℝ → ℝ) (predicted : ℕ → Points n → ℂ)
    (k : ℕ) (s : ℝ) (x : Points n) :
    crop clock predicted (k+1) s x = crop clock predicted k s x +
      (clock s : ℂ)^(k+1) * predicted (k+1) x := by
  unfold crop
  rw [Fin.sum_univ_castSucc]
  rfl

theorem coefficientContinuousOn {n : ℕ} {clock : ℝ → ℝ}
    {actual : ℝ → Points n → ℂ} {predicted : ℕ → Points n → ℂ}
    (positive : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < clock s)
    (jets : CompactShapeCrops clock actual predicted)
    (K : Set (Points n)) (compact : IsCompact K) (clear : K ⊆ WilsonFamily.separated n)
    (k : ℕ) : ContinuousOn (predicted k) K := by
  cases k with
  | zero =>
    obtain ⟨A, _, late⟩ := jets 0 K compact clear
    obtain ⟨s, hs⟩ := late.exists
    intro x hx
    have hh := (hs x hx).2.1.continuousAt
    have eqn : crop clock predicted 0 s = predicted 0 := by
      funext y
      simp [crop]
    rw [eqn] at hh
    exact hh.continuousWithinAt
  | succ k =>
    obtain ⟨A, _, low⟩ := jets k K compact clear
    obtain ⟨B, _, high⟩ := jets (k+1) K compact clear
    obtain ⟨s, hpos, lo, hi⟩ := (positive.and (low.and high)).exists
    have nz : (clock s : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have eqn : predicted (k+1) = fun x =>
        ((clock s : ℂ)^(k+1))⁻¹ *
          (crop clock predicted (k+1) s x - crop clock predicted k s x) := by
      funext x
      rw [nextCrop]
      simp [nz]
    rw [eqn]
    intro x hx
    exact (continuousAt_const.mul ((hi x hx).2.1.continuousAt.sub
      (lo x hx).2.1.continuousAt)).continuousWithinAt

private theorem testIntegrable {n : ℕ} (K : Set (Points n)) (compact : IsCompact K)
    (φ : WilsonFamily.SeparatedTest n) (support : tsupport φ ⊆ K)
    (f : Points n → ℂ) (hf : ContinuousOn f K) :
    Integrable (fun x => φ x * f x) := by
  let w := fun x : Points n => φ x * f x
  have onK : IntegrableOn w K :=
    (φ.continuous.continuousOn.mul hf).integrableOn_compact compact
  have eqn : w = K.indicator w := by
    funext x
    by_cases hx : x ∈ K
    · simp [hx]
    · have hz : φ x = 0 := by
        by_contra hn
        exact hx (support (subset_closure
          (show x ∈ Function.support (fun y : Points n => φ y) from hn)))
      simp [hx, w, hz]
  change Integrable w
  rw [eqn]
  exact onK.integrable_indicator compact.measurableSet

theorem testedOfShapeJets {n : ℕ} {clock : ℝ → ℝ}
    {actual : ℝ → Points n → ℂ} {predicted : ℕ → Points n → ℂ}
    (positive : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < clock s)
    (running : Tendsto clock (𝓝[>] 0) (𝓝 0))
    (jets : CompactShapeCrops clock actual predicted) :
    HasExpansion 0 clock actual predicted := by
  have predInt (φ : WilsonFamily.SeparatedTest n) (k : ℕ) :
      Integrable (fun x => φ x * predicted k x) :=
    testIntegrable (tsupport φ) φ.hasCompactSupport φ Subset.rfl (predicted k)
      (coefficientContinuousOn positive jets (tsupport φ) φ.hasCompactSupport φ.tsupport_subset k)
  refine ⟨predInt, ?_⟩
  intro K compact clear N ε he
  obtain ⟨A, _, late⟩ := jets N K compact clear
  have small : ∀ᶠ s : ℝ in 𝓝[>] 0, A * volume.real K * |clock s| ≤ ε := by
    have hlim : Tendsto (fun s => A * volume.real K * |clock s|) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := A * volume.real K)).mul running.abs
    exact (hlim.eventually_lt_const he).mono fun _ h => h.le
  filter_upwards [late, small] with s hs hsmall
  intro φ support unit
  have ia := testIntegrable K compact φ support (actual s)
    (fun x hx => (hs x hx).1.continuousAt.continuousWithinAt)
  have ib := testIntegrable K compact φ support (crop clock predicted N s)
    (fun x hx => (hs x hx).2.1.continuousAt.continuousWithinAt)
  refine ⟨ia, ?_⟩
  have poly : (∫ x, φ x * crop clock predicted N s x) =
      ∑ k : Fin (N+1), (clock s : ℂ)^k.val * ∫ x, φ x * predicted k.val x := by
    simp_rw [crop, Finset.mul_sum, mul_left_comm (φ _) _ _]
    rw [integral_finsetSum _ (fun k _ => (predInt φ k.val).const_mul _)]
    simp only [integral_const_mul]
  have bound := testedCompactRemainder K compact φ support (actual s)
    (crop clock predicted N s) (A * |clock s|^(N+1)) (unit 0 (le_refl 0))
    (fun x hx => shapeValue (hs x hx))
  rw [← poly, ← integral_sub ia ib]
  have dist : (fun x => φ x * actual s x - φ x * crop clock predicted N s x) =
      (fun x => φ x * (actual s x - crop clock predicted N s x)) := by
    funext x
    ring
  rw [dist]
  calc
    _ ≤ A * |clock s|^(N+1) * volume.real K := bound
    _ = (A * volume.real K * |clock s|) * |clock s|^N := by rw [pow_succ]; ring
    _ ≤ ε * |clock s|^N := mul_le_mul_of_nonneg_right hsmall (pow_nonneg (abs_nonneg _) _)

end YangMills.Matching.CorrelationOnly

