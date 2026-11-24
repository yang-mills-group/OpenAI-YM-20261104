import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! A fixed finite family of real polynomials has one global polynomial
majorant.  Both its positive coefficient and degree precede the family index
and the evaluation point; the empty family is included. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FinitePolynomialFamilyGrowth
open scoped BigOperators

theorem bound {ι : Type*} [Fintype ι] (P : ι → Polynomial ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ (a : ι) (x : ℝ),
      ‖(P a).eval x‖ ≤ C * (1 + ‖x‖) ^ d := by
  classical
  let M : ι → ℝ := fun a =>
    ∑ k ∈ Finset.range ((P a).natDegree + 1), ‖(P a).coeff k‖
  let C : ℝ := 1 + ∑ a, M a
  let d : ℕ := Finset.univ.sup (fun a : ι => (P a).natDegree)
  have hM : ∀ a, 0 ≤ M a := fun a =>
    Finset.sum_nonneg (fun k _ => norm_nonneg ((P a).coeff k))
  have hC : 0 < C := by
    have hsum : 0 ≤ ∑ a, M a :=
      Finset.sum_nonneg (fun a _ => hM a)
    dsimp only [C]
    linarith
  refine ⟨C, hC, d, ?_⟩
  intro a x
  have hd : (P a).natDegree ≤ d :=
    Finset.le_sup (f := fun a : ι => (P a).natDegree) (Finset.mem_univ a)
  have hm : M a ≤ C := by
    have hs : M a ≤ ∑ i, M i :=
      Finset.single_le_sum (fun i _ => hM i) (Finset.mem_univ a)
    dsimp only [C]
    linarith
  have hb : 1 ≤ 1 + ‖x‖ := by
    have hx := norm_nonneg x
    linarith
  have hx : ‖x‖ ≤ 1 + ‖x‖ := by linarith
  rw [Polynomial.eval_eq_sum_range]
  calc
    ‖∑ k ∈ Finset.range ((P a).natDegree + 1), (P a).coeff k * x ^ k‖
        ≤ ∑ k ∈ Finset.range ((P a).natDegree + 1),
          ‖(P a).coeff k * x ^ k‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range ((P a).natDegree + 1),
          ‖(P a).coeff k‖ * ‖x‖ ^ k := by
      simp only [norm_mul, norm_pow]
    _ ≤ ∑ k ∈ Finset.range ((P a).natDegree + 1),
          ‖(P a).coeff k‖ * (1 + ‖x‖) ^ d := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k ≤ d :=
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans hd
      exact mul_le_mul_of_nonneg_left
        ((pow_le_pow_left₀ (norm_nonneg x) hx k).trans
          (pow_le_pow_right₀ hb hk')) (norm_nonneg _)
    _ = M a * (1 + ‖x‖) ^ d := by
      dsimp only [M]
      rw [Finset.sum_mul]
    _ ≤ C * (1 + ‖x‖) ^ d :=
      mul_le_mul_of_nonneg_right hm
        (pow_nonneg (zero_le_one.trans hb) d)

end YM.Integration.FinitePolynomialFamilyGrowth
end
