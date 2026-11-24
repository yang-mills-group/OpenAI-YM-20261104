import YM.Push.STATIONARY_UNIFORM.Scatter
import YM.Extra.ITERATION_NO_LOSS.Sums
import Mathlib.Algebra.BigOperators.Fin

/-! A direct one-port sum for the original Scatter tensor. Scatter itself
uses raw derivatives; the normalized conclusion retains the factorial
explicitly. All prior root summation is already inside the supplied Scatter. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ScatterAnchoredSum

open Lattice RG Push.Uniform
open scoped BigOperators Classical

variable {n : Side} {ι E : Type} [Fintype ι]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {l : ι → Site n} {a C : ℝ} {K N d : ℕ}
variable {f : Positions ι → E} {p : Positions ι}

omit [Fintype ι] in
private theorem exp_insert (j : Fin (d + 1)) (i0 : ι) (q : Fin d → ι) :
    Real.exp (-a * spanSites l (l i0) (Fin.insertNth j i0 q)) =
      ∏ t, Decay a (l i0) (l (q t)) := by
  unfold spanSites
  rw [Fin.sum_univ_succAbove _ j]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, separation_self,
    zero_add, Nat.cast_sum, Finset.mul_sum, Real.exp_sum, Decay]

/-- The raw ordered derivative tensor is summed over every remaining coordinate. -/
theorem raw (H : Scatter l a N f p C) (hl : Multiplicity l K)
    (ha : 0 < a) (hC : 0 ≤ C) (hd : d + 1 ≤ N)
    (j : Fin (d + 1)) (i0 : ι) :
    (∑ q : Fin d → ι, ‖entry f p (Fin.insertNth j i0 q)‖) ≤
      C * ((K : ℝ) * countCost a) ^ d := by
  have ht : SumBudget (fun i : ι => Decay a (l i0) (l i)) ((K : ℝ) * countCost a) := by
    refine ⟨fun _ => (decay_pos ..).le, (hasSum_fintype _).summable, ?_⟩
    rw [tsum_fintype]
    exact hl.count l ha (l i0)
  have hp := Extra.Iteration.Cost.pi (n := d) (fun _ => ht)
  have hsum : (∑ q : Fin d → ι, ∏ t, Decay a (l i0) (l (q t))) ≤
      ((K : ℝ) * countCost a) ^ d := by
    simpa only [tsum_fintype, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hp.2.2
  calc
    _ ≤ ∑ q : Fin d → ι, C * ∏ t, Decay a (l i0) (l (q t)) := by
      apply Finset.sum_le_sum
      intro q _hq
      simpa only [Fin.insertNth_apply_same, exp_insert] using H (d + 1) hd (Fin.insertNth j i0 q) j
    _ = C * ∑ q : Fin d → ι, ∏ t, Decay a (l i0) (l (q t)) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hC

/-- Factorial normalization improves the same original one-port bound. -/
theorem normalized (H : Scatter l a N f p C) (hl : Multiplicity l K)
    (ha : 0 < a) (hC : 0 ≤ C) (hd : d + 1 ≤ N)
    (j : Fin (d + 1)) (i0 : ι) :
    (∑ q : Fin d → ι,
      ‖(((d + 1).factorial : ℝ)⁻¹) • entry f p (Fin.insertNth j i0 q)‖) ≤
      C * ((K : ℝ) * countCost a) ^ d := by
  have hf0 : 0 ≤ (((d + 1).factorial : ℝ)⁻¹) := by positivity
  have hf1 : (((d + 1).factorial : ℝ)⁻¹) ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (d + 1)))
  have hB : 0 ≤ C * ((K : ℝ) * countCost a) ^ d :=
    mul_nonneg hC (pow_nonneg (mul_nonneg (Nat.cast_nonneg K) (count_pos ha).le) d)
  calc
    _ = (((d + 1).factorial : ℝ)⁻¹) *
        (∑ q : Fin d → ι, ‖entry f p (Fin.insertNth j i0 q)‖) := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hf0, Finset.mul_sum]
    _ ≤ (((d + 1).factorial : ℝ)⁻¹) * (C * ((K : ℝ) * countCost a) ^ d) :=
      mul_le_mul_of_nonneg_left (raw H hl ha hC hd j i0) hf0
    _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hf1 hB

end YM.Integration.ScatterAnchoredSum
end
