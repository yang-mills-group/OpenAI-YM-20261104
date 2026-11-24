import YM.Integration.WilsonOrdinaryMixedGram

/-! Price the actual two-radius frame from one fixed finite table of scalar detector pairs. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryMixedDetectors
open Filter Set Spec Climb SharpGram Trace.Pilot WilsonOrdinaryMixedGram
open scoped Topology BigOperators Classical

variable {ι : Type} [Fintype ι] {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private def cost (b : Module.Basis ι ℝ X) := ∑ i : ι, ‖(b.coord i).toContinuousLinearMap‖

private lemma clm_bound (b : Module.Basis ι ℝ X) (f : X →L[ℝ] Y) {A : ℝ} (hA : 0 ≤ A)
    (H : ∀ i : ι, ‖f (b i)‖ ≤ A) : ‖f‖ ≤ cost b * A := by
  classical
  have positive : 0 ≤ cost b := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  apply f.opNorm_le_bound (mul_nonneg positive hA)
  intro x
  have exact_read : f x = ∑ i : ι, (b.coord i x) • f (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum,map_smul,Module.Basis.coord_apply]
  rw [exact_read]
  calc
    _ ≤ ∑ i : ι, ‖(b.coord i x) • f (b i)‖ := norm_sum_le ..
    _ ≤ ∑ i : ι, ‖(b.coord i).toContinuousLinearMap‖ * A * ‖x‖ := by
      apply Finset.sum_le_sum; intro i hi; rw [norm_smul]
      calc
        _ ≤ (‖(b.coord i).toContinuousLinearMap‖ * ‖x‖) * A :=
          mul_le_mul ((b.coord i).toContinuousLinearMap.le_opNorm x) (H i) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = _ := by rw [cost, Finset.sum_mul, Finset.sum_mul]

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (J : ℝ → PhysMS.tower S) (d : ℕ)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field d

/-- The fixed finite roster may be chosen before the real cutoff, the source
radius, the trial truncation and the measured error. This includes every marker
of a real basis, so it tests the physical real-part Gram in its native ordering. -/
theorem read_frame (P : Pier.Lair.Present F J) (b : Module.Basis ι ℝ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ r in trail, ∀ s : ℝ, ∀ A : D →ₗ[ℝ] D, ∀ ε : ℝ, 0 ≤ ε →
      (∀ i j : ι, |mixed F J d r s (b i) (b j) - trial F J d r A (b i) (b j)| ≤ ε) →
      ∀ v : D, ‖(J r d).symm (J s d v) - A v‖ ≤ K * ε * ‖v‖ := by
  obtain ⟨K,hK,read⟩ := WilsonOrdinaryMixedGram.read_frame F J d P
  let T := cost b
  have ht : 0 ≤ T := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨K * max 1 (T*T), mul_pos hK (zero_lt_one.trans_le (le_max_left ..)), ?_⟩
  filter_upwards [read] with r hr s A ε hε scalar v
  let V := mixed F J d r s - trial F J d r A
  have col (i : ι) : ‖V (b i)‖ ≤ T * ε := clm_bound b _ hε (fun j => scalar i j)
  have op : ‖V‖ ≤ T * (T * ε) := clm_bound b V (mul_nonneg ht hε) col
  refine (hr s A v).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg v))
  calc
    K * ‖V‖ ≤ K * (T * (T * ε)) := mul_le_mul_of_nonneg_left op hK.le
    _ = K * (T*T) * ε := by ring
    _ ≤ K * max 1 (T*T) * ε := by gcongr; exact le_max_right ..

end YM.Integration.WilsonOrdinaryMixedDetectors
