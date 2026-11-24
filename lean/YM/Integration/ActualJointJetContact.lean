import YM.Integration.ActualJointJetDetermination
import YM.Comparison.RG02.Assembly.Contact
import Mathlib.Analysis.Analytic.IteratedFDeriv

/-!
Analytic joint derivatives are determined by their diagonal homogeneous jets.
The unit-coupling slice therefore determines the full joint contact order,
provided both sides have the same total degree. The shifted statement retains
one common, explicit marker power. It supplies no physical model replacement.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualJointJetContact
open Function
open Comparison.RG02.Assembly
open scoped BigOperators ContDiff Classical

variable {E W : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Differentiating the normalized diagonal jet recovers the original
symmetric derivative. The factorial is canceled exactly, including order zero. -/
theorem derivative_of_jet (f : E → W)
    (hf : ContDiffAt ℝ ω f 0) (n : ℕ) :
    iteratedFDeriv ℝ n (jet f n) 0 = iteratedFDeriv ℝ n f 0 := by
  ext v
  let A := iteratedFDeriv ℝ n f 0
  have hperm (σ : Equiv.Perm (Fin n)) :
      A (fun i => v (σ i)) = A v := by
    simpa only [A, Function.comp_def] using hf.iteratedFDeriv_comp_perm v σ
  have hfac : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  change iteratedFDeriv ℝ n
    (fun x => ((n.factorial : ℝ)⁻¹ • A) (fun _ => x)) 0 v = A v
  rw [ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal]
  simp only [smul_apply]
  simp_rw [hperm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    mul_inv_cancel₀ hfac, one_smul]

/-- Equality at every unit-coupling direction determines the entire
analytic joint derivative at the same order. -/
theorem derivative_eq_of_unit_slice (f g : ℝ × E → W)
    (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) (n : ℕ)
    (h : ∀ A : E, jet f n (1, A) = jet g n (1, A)) :
    iteratedFDeriv ℝ n f 0 = iteratedFDeriv ℝ n g 0 := by
  have hj : jet f n = jet g n :=
    funext (ActualJointJetDetermination.jet_eq_of_unit_slice f g n h)
  rw [← derivative_of_jet f hf n, ← derivative_of_jet g hg n, hj]

/-- Matching all lower unit-slice jets gives the actual joint vanishing
order of the difference, not just vanishing along each fixed ray. -/
theorem grade_sub_of_unit_slices (f g : ℝ × E → W)
    (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) (k : ℕ)
    (h : ∀ n < k, ∀ A : E, jet f n (1, A) = jet g n (1, A)) :
    GradeAt k (f - g) := by
  refine ⟨hf.sub hg, ?_⟩
  intro n hn
  rw [iteratedFDeriv_sub_apply (hf.of_le le_top) (hg.of_le le_top)]
  exact sub_eq_zero.mpr (derivative_eq_of_unit_slice f g hf hg n (h n hn))

/-- A shared marker power plus the inclusive normalized coefficient range
through r supplies joint contact through that power plus r. -/
theorem grade_sub_of_shifted_slices (f g : ℝ × E → W)
    (b r : ℕ) (hf : GradeAt b f) (hg : GradeAt b g)
    (h : ∀ k ≤ r, ∀ A : E, jet f (b + k) (1, A) = jet g (b + k) (1, A)) :
    GradeAt (b + r + 1) (f - g) := by
  apply grade_sub_of_unit_slices f g hf.smooth hg.smooth
  intro n hn A
  by_cases hlow : n < b
  · rw [hf.jet_z (1, A) hlow, hg.jet_z (1, A) hlow]
  · have hnr : n - b ≤ r := by omega
    have heq : b + (n - b) = n := by omega
    simpa only [heq] using h (n - b) hnr A

/-- A joint contact statement recovers equality of every lower homogeneous
jet when the two functions have their original analytic germs. -/
theorem jet_eq_of_grade_sub (f g : E → W)
    (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0)
    {k n : ℕ} (h : GradeAt k (f - g)) (hn : n < k) (x : E) :
    jet f n x = jet g n x := by
  have hv := h.vanish n hn
  rw [iteratedFDeriv_sub_apply (hf.of_le le_top) (hg.of_le le_top)] at hv
  have he := sub_eq_zero.mp hv
  simp only [jet, he]

end YM.Integration.ActualJointJetContact
end
