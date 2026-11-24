import FormalConversion
import YangMills.CorrelationHierarchy

/-! Smeared expansions, relative-coordinate derivatives and the norm on a finite Maxwell sector. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.Matching

open Filter Set MeasureTheory
open scoped Topology BigOperators Classical

variable {g : GaugeGroup} {B : Maxwell.Reference g}

/-- The coefficient ℓ¹ norm of a Maxwell polynomial. It is independent of the sector cutoff. -/
def coefficientNorm {d : ℕ} (v : B.sector d) : ℝ :=
  ∑ m ∈ v.val.support, ‖MvPolynomial.coeff m v.val‖

theorem coefficientNorm_nonneg {d : ℕ} (v : B.sector d) : 0 ≤ coefficientNorm v :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Each coefficient functional has norm at most one. -/
theorem norm_coeff_le_coefficientNorm {d : ℕ} (v : B.sector d) (m : B.toCoordinates.Key →₀ ℕ) :
    ‖MvPolynomial.coeff m v.val‖ ≤ coefficientNorm v := by
  classical
  by_cases hm : m ∈ v.val.support
  · exact Finset.single_le_sum (fun j _ => norm_nonneg (MvPolynomial.coeff j v.val)) hm
  · rw [MvPolynomial.notMem_support_iff.mp hm, norm_zero]
    exact coefficientNorm_nonneg v

/-- The coefficient norm separates fields at every cutoff. -/
theorem coefficientNorm_eq_zero_iff {d : ℕ} (v : B.sector d) : coefficientNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    apply MvPolynomial.ext
    intro m
    have hle := norm_coeff_le_coefficientNorm v m
    rw [h] at hle
    simpa using norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  · rintro rfl
    simp [coefficientNorm]

/-- The two functions are smooth through order j at x, and each derivative of their difference obeys the bound. -/
def ShapeDerivativeBound {n : ℕ} (j : ℕ) (actual predicted : Points n → ℂ)
    (x : Points n) (bound : ℝ) : Prop :=
  ContDiffAt ℝ j actual x ∧ ContDiffAt ℝ j predicted x ∧
    ∀ l ≤ j, ‖iteratedFDeriv ℝ l (fun y => actual y - predicted y) x‖ ≤ bound

/-- The remainder after order N is little-o of the coupling to power N, uniformly
over separated tests supported in a fixed compact set with derivatives through order m bounded by one. -/
def HasSmearedExpansion {n : ℕ} (m : ℕ) (coupling : ℝ → ℝ) (actual : ℝ → Points n → ℂ)
    (predicted : ℕ → Points n → ℂ) : Prop :=
  (∀ (φ : WilsonFamily.SeparatedTest n) k, Integrable (fun x => φ x * predicted k x)) ∧
  ∀ (K : Set (Points n)), IsCompact K → K ⊆ WilsonFamily.separated n →
    ∀ (N : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ φ : WilsonFamily.SeparatedTest n, tsupport φ ⊆ K →
        (∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j (fun y : Points n => φ y) x‖ ≤ 1) →
        Integrable (fun x => φ x * actual r x) ∧
        ‖(∫ x, φ x * actual r x) - ∑ k : Fin (N + 1),
          (coupling r : ℂ)^k.val * ∫ x, φ x * predicted k.val x‖ ≤ ε * |coupling r|^N

end YangMills.Matching
