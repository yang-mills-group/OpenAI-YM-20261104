import YM.LocalLTE.Weft.Fabric
import Mathlib.Analysis.Calculus.Taylor

/-! Recover a rooted finite polynomial coefficient from the physical
one-parameter samples that are bought by the moving posterior estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionStencil
open Finset Function Set LocalLTE.Weft
open scoped Classical BigOperators

def weight (m : ℕ) (i j : J m) := slate m i j / (probe m i)^m
def cost (m : ℕ) (j : J m) := ∑ i, |weight m i j|

private theorem dual (m : ℕ) (i j : J m) :
    ∑ l, weight m l j * (probe m l)^i.val = if i=j then 1 else 0 := by
  rw [← tally m i j]
  apply sum_congr rfl
  intro l _
  unfold weight mark
  ring

theorem price (m : ℕ) (a : J m → ℝ) (j : J m) (t ε : ℝ)
    (localPrice : ∀ u : J m, |∑ i, a i * (t * probe m u)^i.val| ≤ ε) :
    |a j * t^j.val| ≤ cost m j * ε := by
  have exactRow (i : J m) :
      ∑ u, weight m u j * (a i * (t * probe m u)^i.val) =
        (a i * t^i.val) * (if i=j then 1 else 0) := by
    calc
      _ = ∑ u, (a i * t^i.val) * (weight m u j * (probe m u)^i.val) := by
        apply sum_congr rfl
        intro u _
        rw [mul_pow]
        ring
      _ = _ := by rw [← mul_sum,dual]
  have recovered : ∑ u, weight m u j * (∑ i, a i * (t * probe m u)^i.val) =
      a j * t^j.val := by
    simp_rw [mul_sum]
    rw [sum_comm]
    simp_rw [exactRow]
    simp
  calc
    _ = |∑ u, weight m u j * (∑ i, a i * (t * probe m u)^i.val)| :=
       congrArg abs recovered.symm
    _ ≤ ∑ u, |weight m u j * (∑ i, a i * (t * probe m u)^i.val)| :=
       Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u, |weight m u j| * ε := by
      apply sum_le_sum
      intro u _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (localPrice u) (abs_nonneg _)
    _ = _ := by rw [cost, sum_mul]

end YM.Integration.WilsonPosteriorProjectionStencil

