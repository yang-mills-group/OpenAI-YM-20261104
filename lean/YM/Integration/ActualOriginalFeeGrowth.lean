import YM.Integration.FinitePolynomialFamilyGrowth
import YM.WilsonComparison.Finite.Multiplet
import YM.Integration.ActualRelativeProfileTrial

/-! Quantitative bounds for every calibrated register fee at finite order.
The constants are chosen before all labels in the fixed family, orders up to
the cutoff, Glyphs, and scale arguments. These are the full oil coefficients
used by Dictionary.calibrated; the separate primitive Power component is not
silently included. No analytic input or qlocal payment is assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalFeeGrowth

open MS MS.Land MS.Menus MS.Rake
open PhysicalNext.Repeat.Legato
open scoped Classical BigOperators

variable {G : Gauge} (B : MS.Local.Physical.Deck G) (Q : Land.Prescription B)
    {W : Type*} [Fintype W] (u : W → Label B) (K : ℕ)

/-- One genuine polynomial bound for the complete calibrated fee family
through order K; no degree bound independent of K is asserted. -/
theorem bound :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ,
      ∀ (i : W) (k : ℕ), k ≤ K → ∀ (g : Glyph B (u i).h) (x : ℝ),
        ‖oil (Q.fees (u i).h (u i).item) g k x‖ ≤ C * (1 + ‖x‖) ^ d := by
  classical
  let I := Σ i : W, Fin (K + 1) × Glyph B (u i).h
  let P : I → Polynomial ℝ := fun a =>
    ((Q.fees (u a.1).h (u a.1).item) a.2.1.val).register a.2.2
  obtain ⟨C, hC, d, h⟩ := FinitePolynomialFamilyGrowth.bound P
  refine ⟨C, hC, d, ?_⟩
  intro i k hk g x
  have hh := h ⟨i, ⟨⟨k, Nat.lt_succ_of_le hk⟩, g⟩⟩ x
  simpa only [P, oil, Complex.norm_real] using hh

/-- At a fixed physical scale mu, shifting the complete register polynomial
changes only the constant; the bound is uniform in the running clock. -/
theorem shifted_bound (μ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ,
      ∀ (i : W) (k : ℕ), k ≤ K → ∀ (g : Glyph B (u i).h) (t : ℝ),
        ‖oil (Q.fees (u i).h (u i).item) g k (μ - t)‖ ≤ C * (1 + ‖t‖) ^ d := by
  obtain ⟨C, hC, d, h⟩ := bound B Q u K
  refine ⟨C * (1 + ‖μ‖) ^ d, mul_pos hC (pow_pos (by positivity) d), d, ?_⟩
  intro i k hk g t
  have hbase : 1 + ‖μ - t‖ ≤ (1 + ‖μ‖) * (1 + ‖t‖) := by
    have ht := norm_sub_le μ t
    have hp := mul_nonneg (norm_nonneg μ) (norm_nonneg t)
    nlinarith
  calc
    ‖oil (Q.fees (u i).h (u i).item) g k (μ - t)‖ ≤
        C * (1 + ‖μ - t‖) ^ d := h i k hk g (μ - t)
    _ ≤ C * ((1 + ‖μ‖) * (1 + ‖t‖)) ^ d :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase d) hC.le
    _ = (C * (1 + ‖μ‖) ^ d) * (1 + ‖t‖) ^ d := by
      rw [mul_pow]
      ring

/-- All finite products of calibrated coefficients have an explicit bound
on the original Run's clock. The insertion count and degree remain visible;
the constants do not depend on the level, selected Glyphs or coefficient orders. -/
theorem clock_products (R : Run G) (μ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ,
      ∀ (N : ℕ) (s : Finset W) (k : W → ℕ) (g : ∀ i, Glyph B (u i).h),
        (∀ i ∈ s, k i ≤ K) →
        ‖∏ i ∈ s, oil (Q.fees (u i).h (u i).item) (g i) (k i)
            (μ - R.family.S.scale N)‖ ≤
          C ^ s.card * (1 + ‖R.family.S.scale N‖) ^ (d * s.card) := by
  classical
  obtain ⟨C, hC, d, h⟩ := shifted_bound B Q u K μ
  refine ⟨C, hC, d, ?_⟩
  intro N s k g hk
  rw [norm_prod]
  calc
    ∏ i ∈ s, ‖oil (Q.fees (u i).h (u i).item) (g i) (k i)
        (μ - R.family.S.scale N)‖ ≤
        ∏ _i ∈ s, C * (1 + ‖R.family.S.scale N‖) ^ d :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i hi =>
        h i (k i) (hk i hi) (g i) (R.family.S.scale N)
    _ = C ^ s.card * (1 + ‖R.family.S.scale N‖) ^ (d * s.card) := by
      rw [Finset.prod_const, mul_pow, ← pow_mul]

end YM.Integration.ActualOriginalFeeGrowth
end
