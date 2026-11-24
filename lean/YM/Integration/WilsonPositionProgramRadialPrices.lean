import YM.QuadraticLocal.Rebirth.Mouth
import Mathlib.LinearAlgebra.Lagrange

/-! A finite set of real dilations prices every homogeneous part of a filed angular row. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramRadialPrices
open Finset Polynomial Comparison.RG02 Comparison.RG02.Assembly Comparison.RG02.Valence
open scoped Classical BigOperators
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def factor (D k a:ℕ):ℂ:=
  (Lagrange.basis (Finset.range (D+1)) ((↑):ℕ→ℂ) a).coeff k

private theorem coefficient (D k:ℕ)(u:ℕ→ℂ)(hk:k≤D):
    u k=∑ a∈range (D+1), factor D k a * (∑ j∈range (D+1), (a:ℂ)^j * u j):=by
  let P:Polynomial ℂ:=∑ j∈range (D+1),Polynomial.monomial j (u j)
  have degree:P.natDegree≤D:=by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact (Polynomial.natDegree_monomial_le (u j)).trans (mem_range_succ_iff.mp hj)
  have small:P.degree<(D+1:ℕ):=Polynomial.degree_le_natDegree.trans_lt
    (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le degree))
  have same:=congrArg (fun q:Polynomial ℂ=>q.coeff k)
    (Lagrange.eq_interpolate (s:=range (D+1)) (v:=((↑):ℕ→ℂ)) Nat.cast_injective.injOn
      (f:=P) (by simpa using small))
  have left:P.coeff k=u k:=by
    simp [P,Polynomial.coeff_monomial,hk]
  rw [left] at same
  change u k=(∑ a∈range (D+1),Polynomial.C (P.eval (a:ℂ)) *
    Lagrange.basis (range (D+1)) ((↑):ℕ→ℂ) a).coeff k at same
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul] at same
  simpa [factor,P,Polynomial.eval_finsetSum,mul_comm] using same

theorem centered (D k:ℕ)(hk:k≤D)(F:E→ℂ)(paid:Level D F)(x y:E):
    Assembly.jet F k x-Assembly.jet F k y=
      ∑ a∈range (D+1),factor D k a * (F ((a:ℝ) • x)-F ((a:ℝ) • y)):=by
  rw [coefficient D k (fun j=>Assembly.jet F j x-Assembly.jet F j y) hk]
  apply sum_congr rfl
  intro a _
  rw [paid.posted ((a:ℝ) • x),paid.posted ((a:ℝ) • y),←sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro j _
  simp [Clipper.weight,Complex.real_smul,mul_sub]

end YM.Integration.WilsonPositionProgramRadialPrices
end
