import Mathlib.RingTheory.PowerSeries.Inverse
import MSScalarInverse
import MSGradeProjection

/-! # Formal field series on the free polynomial sectors

Composition is ordered from right to left on input fields. Each coefficient
uses only the coefficients through the specified order. A normalized constant
term gives the two-sided inverse. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.MSbar.Series

open scoped BigOperators
open PowerSeries

variable {g : GaugeGroup} (B : Maxwell.Reference g)

abbrev Frame := (d k : ℕ) → Module.End ℂ (B.sector d)

/-- The coefficient of the product of two endomorphism series. -/
def cauchy (A C : Frame B) : Frame B := fun d k =>
  ∑ i : Fin (k + 1), (A d i.val).comp (C d (k - i.val))

/-- Coefficients of the formal inverse at the unit leading endomorphism. -/
def inverseFrame (A : Frame B) : Frame B := fun d k =>
  coeff k (invOfUnit (PowerSeries.mk (A d)) 1)

/-- The position coupling is substituted into the MS field series. -/
def reparametrize (f : ℕ → ℝ) (L : Frame B) : Frame B := fun d k =>
  ∑ j : Fin (k + 1), (Matching.couplingPower f j.val k : ℂ) • L d j.val

/-- Select the blocks between fields of equal engineering weight. -/
def gradeFrame (D : Frame B) : Frame B := fun d k =>
  Matching.Grade.diagonal B d (D d k)

/-- The finite adjustment satisfies D N = Z when D has identity constant term. -/
def adjustment (D : Frame B) : Frame B :=
  cauchy B (inverseFrame B D) (gradeFrame B D)

private theorem coeff_cauchy (A C : Frame B) (d k : ℕ) :
    coeff k (PowerSeries.mk (A d) * PowerSeries.mk (C d)) = cauchy B A C d k := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  let term := fun i : ℕ => (A d i) * (C d (k - i))
  change _ = ∑ i : Fin (k + 1), term i.val
  rw [Fin.sum_univ_eq_sum_range]
  simp only [coeff_mk]
  rfl

private theorem inverse_series (A : Frame B) (d : ℕ) :
    PowerSeries.mk (inverseFrame B A d) = invOfUnit (PowerSeries.mk (A d)) 1 := by
  ext k
  rw [coeff_mk]
  rfl

private theorem cauchy_series (A C : Frame B) (d : ℕ) :
    PowerSeries.mk (cauchy B A C d) = PowerSeries.mk (A d) * PowerSeries.mk (C d) := by
  ext k
  rw [coeff_mk, coeff_cauchy]

attribute [local irreducible] cauchy inverseFrame gradeFrame PowerSeries.invOfUnit

private theorem product_eq_identity (A C : Frame B) (d k : ℕ)
    (eq : PowerSeries.mk (A d) * PowerSeries.mk (C d) = 1) :
    cauchy B A C d k = if k = 0 then LinearMap.id else 0 := by
  rw [← coeff_cauchy B A C d k, eq, coeff_one]
  rfl

/-- The two orders of multiplication give the identity at each coefficient. -/
theorem inverseFrame_products (A : Frame B) (lead : ∀ d, A d 0 = LinearMap.id) (d k : ℕ) :
    cauchy B (inverseFrame B A) A d k = (if k = 0 then LinearMap.id else 0) ∧
    cauchy B A (inverseFrame B A) d k = (if k = 0 then LinearMap.id else 0) := by
  have h : constantCoeff (PowerSeries.mk (A d)) = (1 : (Module.End ℂ (B.sector d))ˣ) := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    exact lead d
  constructor
  · apply product_eq_identity B
    rw [inverse_series B A d]
    exact invOfUnit_mul (PowerSeries.mk (A d)) 1 h
  · apply product_eq_identity B
    rw [inverse_series B A d]
    exact mul_invOfUnit (PowerSeries.mk (A d)) 1 h

/-- Multiplication by the computed adjustment removes exactly the off-diagonal blocks. -/
theorem cauchy_adjustment (D : Frame B) (lead : ∀ d, D d 0 = LinearMap.id) (d k : ℕ) :
    cauchy B D (adjustment B D) d k = gradeFrame B D d k := by
  have h : constantCoeff (PowerSeries.mk (D d)) = (1 : (Module.End ℂ (B.sector d))ˣ) := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    exact lead d
  have cancels := mul_invOfUnit (PowerSeries.mk (D d)) 1 h
  rw [← coeff_cauchy B D (adjustment B D) d k, adjustment,
    cauchy_series B (inverseFrame B D) (gradeFrame B D) d, inverse_series B D d,
    ← mul_assoc, cancels, one_mul, coeff_mk]

theorem reparametrize_zero (f : ℕ → ℝ) (L : Frame B) (d : ℕ) :
    reparametrize B f L d 0 = L d 0 := by
  simp [reparametrize, Matching.couplingPower]

end YangMills.MSbar.Series
