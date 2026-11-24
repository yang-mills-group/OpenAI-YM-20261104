import YM.GradedFar.Width
/-!
# Tariff for using the cropped FarCoefficients vector as input to the (true and predicted) operators at center

Fixed compact Near shapes, uniform in the actual basis norm of the whole Sec
vector under evaluation. The same hypotheses as in the second inequality of M.2. Useful
in M.3 and for recropping the final measured comparison in M.4.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set PowerSeries
open XSpace XSpace.Normalize XSpace.Structure1 Scale
open MS Dframe O O.Score O.Enh
open scoped Topology BigOperators Classical

variable {G : Gauge} {n h : ℕ} {d : Fin n → ℕ}
    {A : Arenas G} {F : ℝ → Frames G} {ψ : ℝ → PowerSeries ℂ}
    (H : Canon.Physical A ψ F)
    {K : Set (Points n)} (hK : IsCompact K) (hx : K ⊆ conf n)

lemma width_sum {I : Type*} (s : Finset I) (f : I → Sec G h) : width (∑ i ∈ s, f i) ≤ ∑ i ∈ s, width (f i) := by
  unfold width; rw [map_sum]; exact norm_sum_le ..
include H hK hx
lemma vector_coeff_cap (h j : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ u : Inputs G d, Box u L → width (opeVector A h u x j) ≤ C := by
  choose C hC using fun q : Toon G h => uniform_opeCoeff (d:=d) H hK hx (Dframe.flash q) j hL
  refine ⟨max (∑ i, C i) 0, le_max_right .., fun x hX u hu => ?_⟩
  apply le_trans (width_sum ..); refine (Finset.sum_le_sum fun i _=>?_).trans (le_max_left (∑ i, C i) 0)
  rw [width_smul, basis_width, mul_one]; exact hC i x hX u hu
lemma vector_cap (h p : ℕ) (L : ℝ) (hL : 0 ≤ L) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ u : Inputs G d,
    Box u L → ∀ z : ℝ, |z| ≤ 1 → width (croppedVector A h p u x z) ≤ C := by
  choose C hC H using fun i => vector_coeff_cap (d:=d) H hK hx h i L hL
  refine ⟨∑ i ∈ Finset.range (p+1), C i, Finset.sum_nonneg (fun i _=> hC i), fun x hX u hu z hz => ?_⟩
  rw [croppedVector_series]; apply le_trans (width_sum ..); refine Finset.sum_le_sum fun i _ => ?_
  rw [width_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul (pow_le_one₀ (abs_nonneg z) hz) (H i x hX u hu) (width_nn _) zero_le_one).trans_eq (one_mul _)
lemma crop_cap {p q : ℕ} (h : ℕ) (hp : p ≤ q) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ u : Inputs G d, Box u L → ∀ z : ℝ, |z| ≤ 1 →
      width (croppedVector A h q u x z - croppedVector A h p u x z) ≤ C * |z|^(p+1) := by
  choose C hC H using fun i => vector_coeff_cap (d:=d) H hK hx h i L hL
  refine ⟨∑ i ∈ Finset.Ico (p+1) (q+1), C i, Finset.sum_nonneg (fun i _=> hC i),
    fun x hX u hu z hz => ?_⟩
  rw [croppedVector_series, croppedVector_series, ← Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ hp)]
  apply le_trans (width_sum ..); rw [Finset.sum_mul]; refine Finset.sum_le_sum fun i hi=>?_
  rw [width_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_comm (C i)]
  exact mul_le_mul (pow_le_pow_of_le_one (abs_nonneg z) hz (Finset.mem_Ico.mp hi).1) (H i x hX u hu)
    (width_nn _) (pow_nonneg (abs_nonneg z) _)
end YM.FVA2.GradedFar
