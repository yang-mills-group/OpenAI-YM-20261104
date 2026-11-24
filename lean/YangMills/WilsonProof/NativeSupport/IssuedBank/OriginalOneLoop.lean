import YangMills.WilsonProof.NativeSupport.IssuedBank.OriginalCasimir

set_option autoImplicit false

namespace IssuedBank.OriginalOneLoop

open YangMills YangMills.Wilson IssuedBank.OriginalCasimir
open scoped BigOperators
noncomputable section

variable {g : GaugeGroup} (B : Maxwell.Reference g)

private abbrev axis (i : Fin B.m) : Maxwell.Color B.m := EuclideanSpace.single i 1

private theorem matrixExpansion (x : Maxwell.Color B.m) :
    (∑ i, x i • B.matrix (axis B i)) = B.matrix x := by
  have expanded : (∑ i, x i • axis B i) = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin B.m) ℝ).sum_repr x
  simpa only [map_sum, map_smul] using congrArg B.matrix expanded

theorem occupied (hg : g.IsSimple) :
    ∃ i j : Fin B.m, bracket B (axis B i) (axis B j) ≠ 0 := by
  classical
  by_contra empty
  push Not at empty
  obtain ⟨X, hX, Y, hY, witness⟩ := hg.1
  rw [← B.colors] at hX hY
  obtain ⟨x, rfl⟩ := hX
  obtain ⟨y, rfl⟩ := hY
  apply witness
  rw [sub_eq_zero, ← matrixExpansion B x, ← matrixExpansion B y]
  apply Commute.sum_left
  intro i _
  apply Commute.sum_right
  intro j _
  have entry : Commute (B.matrix (axis B i)) (B.matrix (axis B j)) :=
    sub_eq_zero.mp (empty i j)
  exact (entry.smul_left (x i)).smul_right (y j)

theorem original (hg : g.IsSimple) : 0 < wilsonOneLoop B := by
  obtain ⟨i, j, paid⟩ := occupied B hg
  let charge (a b : Fin B.m) : ℝ :=
    -((bracket B (axis B a) (axis B b) * bracket B (axis B a) (axis B b)).trace).re
  have free (a b : Fin B.m) : 0 ≤ charge a b := nonnegative B _ _
  have income : 0 < charge i j := positiveOn B _ _ paid
  have total : 0 < ∑ a, ∑ b, charge a b :=
    Finset.sum_pos' (fun a _ => Finset.sum_nonneg (fun b _ => free a b))
      ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun b _ => free i b) ⟨j, Finset.mem_univ _, income⟩⟩
  have count : 0 < (B.m : ℝ) := by exact_mod_cast (Nat.zero_le i.val).trans_lt i.isLt
  change 0 < 11 * ((∑ a, ∑ b, charge a b) / (((g.n+1 : ℕ) : ℝ) * (B.m : ℝ))) / (48 * Real.pi ^ 2)
  exact div_pos (mul_pos (by norm_num) (div_pos total (mul_pos (by positivity) count))) (by positivity)


end
end IssuedBank.OriginalOneLoop
