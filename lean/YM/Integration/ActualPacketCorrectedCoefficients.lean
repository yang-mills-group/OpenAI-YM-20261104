import YM.Integration.ActualPacketAdaptiveCopies
import YM.Integration.ActualBetaAllOrderCost
import Mathlib.Data.Fintype.BigOperators

/-!
The exact row coefficients for the actual beta-reset interpolation.
The polynomial copies have j < n(e); the correcting copy has j = n(e).
All remaining grid entries vanish. Zero truncation order is retained.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualPacketCorrectedCoefficients
open ActualPacketAdaptiveCopies ActualBetaCutoff ActualBetaRemainder
open scoped BigOperators

def rowCoefficient (r : ℕ) (delta physical : ℝ) (e : ℤ)
    (j : Fin (grid r + 1)) : ℝ :=
  if j.val < retuningOrder r e then coefficient e j.val * delta ^ j.val
  else if j.val = retuningOrder r e then
    correctionCoefficient e delta physical (retuningOrder r e)
  else 0

def normalizedCoefficient (r : ℕ) (delta physical : ℝ) (e : ℤ)
    (j : Fin (grid r + 1)) : ℂ :=
  ((unit delta physical : ℂ) ^ e)⁻¹ * (rowCoefficient r delta physical e j : ℂ)

private theorem finite_splice (m n : ℕ) (hn : n ≤ m) (f : ℕ → ℝ) (z : ℝ) :
    (∑ j : Fin (m + 1), if j.val < n then f j.val
      else if j.val = n then z else 0) = (∑ j ∈ Finset.range n, f j) + z := by
  classical
  have hsplit (j : Fin (m + 1)) :
      (if j.val < n then f j.val else if j.val = n then z else 0) =
      (if j.val < n then f j.val else 0) + (if j.val = n then z else 0) := by
    by_cases hj : j.val < n
    · simp [hj, Nat.ne_of_lt hj]
    · simp [hj]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  have hfirst :
      (∑ j : Fin (m + 1), if j.val < n then f j.val else 0) =
      ∑ j ∈ Finset.range n, f j := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < n then f j else 0) (m + 1)]
    symm
    calc
      (∑ j ∈ Finset.range n, f j) =
          ∑ j ∈ Finset.range n, if j < n then f j else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [if_pos (Finset.mem_range.mp hj)]
      _ = ∑ j ∈ Finset.range (m + 1), if j < n then f j else 0 := by
        apply Finset.sum_subset (Finset.range_mono (Nat.le_succ_of_le hn))
        intro j _hj hnot
        exact if_neg (fun hj => hnot (Finset.mem_range.mpr hj))
  have hlast : (∑ j : Fin (m + 1), if j.val = n then z else 0) = z := by
    let j0 : Fin (m + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
    rw [Finset.sum_eq_single j0]
    · simp [j0]
    · intro j _hj hj
      have hne : j.val ≠ n := fun h => hj (Fin.ext h)
      exact if_neg hne
    · intro h
      exact False.elim (h (Finset.mem_univ j0))
  rw [hfirst, hlast]

/-- Every copy above the row-dependent cutoff has zero coefficient. -/
theorem rowCoefficient_zero (r : ℕ) (delta physical : ℝ) (e : ℤ)
    (j : Fin (grid r + 1)) (hj : retuningOrder r e < j.val) :
    rowCoefficient r delta physical e j = 0 := by
  have hlt : ¬ j.val < retuningOrder r e := by omega
  have heq : j.val ≠ retuningOrder r e := by omega
  simp only [rowCoefficient, if_neg hlt, if_neg heq]

/-- The exact finite scalar is the original corrected Taylor polynomial. -/
theorem row_sum (r : ℕ) (delta physical g : ℝ) (e : ℤ) :
    (∑ j : Fin (grid r + 1),
      rowCoefficient r delta physical e j * g ^ (2 * j.val)) =
      corrected e delta physical (retuningOrder r e) g := by
  have hterm (j : Fin (grid r + 1)) :
      rowCoefficient r delta physical e j * g ^ (2 * j.val) =
      if j.val < retuningOrder r e then
        coefficient e j.val * delta ^ j.val * g ^ (2 * j.val)
      else if j.val = retuningOrder r e then
        correctionCoefficient e delta physical (retuningOrder r e) *
          g ^ (2 * retuningOrder r e)
      else 0 := by
    by_cases hj : j.val < retuningOrder r e
    · simp [rowCoefficient, hj]
    · by_cases he : j.val = retuningOrder r e
      · simp [rowCoefficient, he]
      · simp [rowCoefficient, hj, he]
  simp_rw [hterm]
  rw [finite_splice (grid r) (retuningOrder r e) (grid_bound r e)
    (fun j : ℕ => coefficient e j * delta ^ j * g ^ (2 * j))
    (correctionCoefficient e delta physical (retuningOrder r e) *
      g ^ (2 * retuningOrder r e))]
  rw [corrected, truncated_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [mul_pow, ← pow_mul]
  ring

/-- Complex scalar version used by the literal token series. -/
theorem row_complex_sum (r : ℕ) (delta physical g : ℝ) (e : ℤ) :
    (∑ j : Fin (grid r + 1),
      (rowCoefficient r delta physical e j : ℂ) * (g : ℂ) ^ (2 * j.val)) =
      (corrected e delta physical (retuningOrder r e) g : ℂ) := by
  exact_mod_cast row_sum r delta physical g e

/-- The actual triangle bill retains the full correcting copy, also at n=0. -/
theorem row_bill (r : ℕ) (delta physical g : ℝ) (e : ℤ) :
    (∑ j : Fin (grid r + 1),
      |rowCoefficient r delta physical e j| * |g| ^ (2 * j.val)) =
      coefficientBill e delta g (retuningOrder r e) +
        |correctionCoefficient e delta physical (retuningOrder r e)| *
          |g| ^ (2 * retuningOrder r e) := by
  have hterm (j : Fin (grid r + 1)) :
      |rowCoefficient r delta physical e j| * |g| ^ (2 * j.val) =
      if j.val < retuningOrder r e then
        |coefficient e j.val| * |delta| ^ j.val * |g| ^ (2 * j.val)
      else if j.val = retuningOrder r e then
        |correctionCoefficient e delta physical (retuningOrder r e)| *
          |g| ^ (2 * retuningOrder r e)
      else 0 := by
    by_cases hj : j.val < retuningOrder r e
    · simp [rowCoefficient, hj, abs_mul, abs_pow]
    · by_cases he : j.val = retuningOrder r e
      · simp [rowCoefficient, he]
      · simp [rowCoefficient, hj, he]
  simp_rw [hterm]
  simpa only [coefficientBill] using
    finite_splice (grid r) (retuningOrder r e) (grid_bound r e)
      (fun j : ℕ => |coefficient e j| * |delta| ^ j * |g| ^ (2 * j))
      (|correctionCoefficient e delta physical (retuningOrder r e)| *
        |g| ^ (2 * retuningOrder r e))

theorem normalizedCoefficient_zero (r : ℕ) (delta physical : ℝ) (e : ℤ)
    (j : Fin (grid r + 1)) (hj : retuningOrder r e < j.val) :
    normalizedCoefficient r delta physical e j = 0 := by
  simp only [normalizedCoefficient, rowCoefficient_zero r delta physical e j hj,
    Complex.ofReal_zero, mul_zero]

/-- Literal scalar normalization of the copies; no signed-power regrouping. -/
theorem normalized_sum (r : ℕ) (delta physical g : ℝ) (e : ℤ) :
    (∑ j : Fin (grid r + 1),
      normalizedCoefficient r delta physical e j * (g : ℂ) ^ (2 * j.val)) =
      ((unit delta physical : ℂ) ^ e)⁻¹ *
        (corrected e delta physical (retuningOrder r e) g : ℂ) := by
  simp only [normalizedCoefficient, mul_assoc, ← Finset.mul_sum, row_complex_sum]

/-- The fixed retune followed by these copies is exactly one at the
physical point. The original positive-radicand domain is explicit. -/
theorem normalized_at_physical (r : ℕ) (delta physical : ℝ) (e : ℤ)
    (hg : physical ≠ 0) (hdom : 0 < 1 - delta * physical ^ 2) :
    (∑ j : Fin (grid r + 1),
      normalizedCoefficient r delta physical e j *
        (physical : ℂ) ^ (2 * j.val)) = 1 := by
  rw [normalized_sum, corrected_at_physical e delta physical (retuningOrder r e) hg]
  have hu : unit delta physical ≠ 0 :=
    ne_of_gt (inv_pos.mpr (Real.sqrt_pos.mpr hdom))
  have huc : (unit delta physical : ℂ) ≠ 0 := by exact_mod_cast hu
  have hcast : ((unit delta physical ^ e : ℝ) : ℂ) =
      (unit delta physical : ℂ) ^ e := by norm_cast
  rw [hcast]
  exact inv_mul_cancel₀ (zpow_ne_zero e huc)

/-- Complete normalized coefficient price at the physical point. -/
theorem normalized_bill (r : ℕ) (delta physical : ℝ) (e : ℤ) :
    (∑ j : Fin (grid r + 1),
      ‖normalizedCoefficient r delta physical e j‖ *
        ‖(physical : ℂ) ^ (2 * j.val)‖) =
      |(unit delta physical ^ e)⁻¹| *
        (coefficientBill e delta physical (retuningOrder r e) +
          |correctionCoefficient e delta physical (retuningOrder r e)| *
            |physical| ^ (2 * retuningOrder r e)) := by
  have hcast : ((unit delta physical : ℂ) ^ e)⁻¹ =
      (((unit delta physical ^ e)⁻¹ : ℝ) : ℂ) := by norm_cast
  simp only [normalizedCoefficient, hcast, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, mul_assoc, ← Finset.mul_sum, row_bill]

/-- A cap-only constant pays every row and every requested order with
leading constant one. No factor counting powers or copies appears. -/
theorem normalized_uniform_bill (cap : ℕ) :
    ∃ C > 0, ∀ e : ℤ, |e| ≤ (cap : ℤ) → ∀ delta physical : ℝ,
      physical ≠ 0 → |delta * physical ^ 2| ≤ 1 / 2 → ∀ r : ℕ,
      (∑ j : Fin (grid r + 1),
        ‖normalizedCoefficient r delta physical e j‖ *
          ‖(physical : ℂ) ^ (2 * j.val)‖) ≤
        1 + C * |delta * physical ^ 2| := by
  obtain ⟨D, hD, hbill⟩ := full_retuning_all_orders cap
  obtain ⟨B, hB, hunit⟩ := ActualBetaUnitFirstOrder.unit_and_inverse_bounds cap
  refine ⟨D + B + D * B / 2, by positivity, ?_⟩
  intro e he delta physical hg hsmall r
  rw [normalized_bill]
  have hnonneg : 0 ≤ coefficientBill e delta physical (retuningOrder r e) +
      |correctionCoefficient e delta physical (retuningOrder r e)| *
        |physical| ^ (2 * retuningOrder r e) := by
    unfold coefficientBill
    positivity
  calc
    _ ≤ (1 + B * |delta * physical ^ 2|) *
        (1 + D * |delta * physical ^ 2|) :=
      mul_le_mul (hunit e he delta physical hsmall).2
        (hbill e he delta physical hg hsmall (retuningOrder r e))
        hnonneg (by positivity)
    _ ≤ 1 + (D + B + D * B / 2) * |delta * physical ^ 2| := by
      have hquad := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hsmall (abs_nonneg (delta * physical ^ 2)))
        (mul_nonneg hB.le hD.le)
      nlinarith

end YM.Integration.ActualPacketCorrectedCoefficients
end
