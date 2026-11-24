import YM.Integration.WilsonLongContactPriorHeld
import YM.Integration.ActualTrajectoryTransport

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactPriorRoots
open Lattice RG Finset
open scoped Classical BigOperators
variable {ι:Type} [Fintype ι] {n:Side} (X:ℕ→Support n) (B:ℕ) (a:ℝ)

def field (Z:Support n) (selected:Finset ℕ) (k:ℕ) (d:ℕ→Finset ι→ℝ) (φ:ℕ→Finset ι→ℂ):ℂ:=
  ∑ i∈Ac.buds X selected Z,∑ t:Finset ι,if t.card≤k then φ i t*(d i t:ℂ) else 0

private theorem mode {i:ℕ} {k:ℕ} {d c:Finset ι→ℝ} {φ:Finset ι→ℂ}
    (bound:∀t,‖d t‖≤c t) (test:∀t,‖φ t‖≤Real.exp (a*Lattice.coverNumber B (X i))):
    ‖∑t:Finset ι,if t.card≤k then φ t*(d t:ℂ) else 0‖≤
       (∑t:Finset ι,if t.card≤k then c t else 0)*Real.exp (a*Lattice.coverNumber B (X i)):=by
  classical
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro t _
  by_cases h:t.card≤k
  · simp only [if_pos h,norm_mul,Complex.norm_real]
    exact (mul_le_mul (test t) (bound t) (norm_nonneg _) (Real.exp_nonneg _)).trans (le_of_eq (mul_comm _ _))
  · simp only [if_neg h,norm_zero,zero_mul,le_refl]

theorem observed (Z:Support n) (selected:Finset ℕ) {k:ℕ} {w:ℝ} (d c:ℕ→Finset ι→ℝ)
    (φ:ℕ→Finset ι→ℂ) (fd:∀i t,‖d i t‖≤c i t)
    (test:∀i t,‖φ i t‖≤Real.exp (a*Lattice.coverNumber B (X i)))
    (fee:Ac.Hit X B (fun i=>∑t:Finset ι,if t.card≤k then c i t else 0) a w):
    ‖field X Z selected k d φ‖≤(Z.card:ℝ)*w:=by
  classical
  refine (norm_sum_le _ _).trans ?_
  exact (Finset.sum_le_sum (fun i _=>mode X B a (fd i) (test i))).trans (Ac.demand X B fee Z selected)

end YM.Integration.WilsonLongContactPriorRoots
