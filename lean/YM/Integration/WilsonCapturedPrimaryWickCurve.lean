import YM.Integration.WilsonCapturedPrimaryPotential
import YM.Integration.WilsonFirstReceivedRadialForecast

/-! Evaluate an independently filed finite homogeneous jet on the actual
polynomial curve of held link angles used by the field detector. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWickCurve
open Finset Comparison.RG02
open scoped Classical BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pull (f : E → ℂ) (D d : ℕ) (v : Fin (d+1) → E) : Polynomial ℂ :=
  ∑ k∈range (D+1), ∑ a : Fin k → Fin (d+1),
    Polynomial.monomial (∑ j, (a j).val)
      ((k.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ k f 0 (v ∘ a))

theorem bound (f : E → ℂ) (D d : ℕ) (v : Fin (d+1) → E) :
    (pull f D d v).natDegree ≤ D*d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a _
  apply (Polynomial.natDegree_monomial_le ..).trans
  calc
    ∑ j : Fin k, (a j).val ≤ ∑ _ : Fin k, d := sum_le_sum fun j _ => Nat.le_of_lt_succ (a j).isLt
    _ = k*d := by simp
    _ ≤ D*d := Nat.mul_le_mul_right d (Nat.le_of_lt_succ (mem_range.mp hk))

theorem evaluated (f : E → ℂ) {D d : ℕ} (h : Valence.Level (D:ℤ) f)
    (v : Fin (d+1) → E) (t : ℝ) :
    (pull f D d v).eval (t:ℂ) = f (∑ j, t^j.val • v j) := by
  rw [h.posted]
  simp only [pull,Polynomial.eval_finsetSum,Polynomial.eval_monomial]
  apply sum_congr rfl
  intro k _
  let T := iteratedFDeriv ℝ k f 0
  change _ = (k.factorial:ℝ)⁻¹ • T (fun _ => ∑ j : Fin (d+1), t^j.val • v j)
  rw [T.map_sum_finset (fun (_ : Fin k) (j : Fin (d+1)) => t^j.val • v j) (fun _=>univ),
    Fintype.piFinset_univ,Finset.smul_sum]
  apply sum_congr rfl
  intro a _
  rw [T.map_smul_univ]
  simp only [Complex.real_smul, Complex.ofReal_prod,Complex.ofReal_pow,← Finset.prod_pow_eq_pow_sum]
  dsimp only [T,Function.comp_def]
  ring

end YM.Integration.WilsonCapturedPrimaryWickCurve
