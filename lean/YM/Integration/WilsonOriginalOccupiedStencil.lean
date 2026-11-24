import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The real taps 0,T,...,nT withdraw the value at 1 minus the actual constant tap. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedStencil
open Finset Polynomial
open scoped BigOperators Classical
def node {n:ℕ}(i:Fin (n+1)):ℂ:=(i.val:ℂ)
def basis {n:ℕ}(i:Fin (n+1)):Polynomial ℂ := Lagrange.basis univ node i
def weight {n:ℕ}(q:ℂ)(i:Fin (n+1)):ℂ:=(basis i).eval q-(basis i).eval 0

private theorem read {n:ℕ}(p:Polynomial ℂ)(size:p.natDegree ≤ n)(z:ℂ):
    p.eval z=∑i:Fin (n+1), p.eval (node i)*(basis i).eval z:=by
  have inj: Set.InjOn (node (n:=n)) (↑(univ:Finset (Fin (n+1)))):=by
    intro i _ j _ eq
    apply Fin.ext
    unfold node at eq
    exact_mod_cast eq
  have deg:p.degree < (univ:Finset (Fin (n+1))).card:=by
    simp only [card_univ,Fintype.card_fin]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le size)
  nth_rw 1 [Lagrange.eq_interpolate inj deg]
  rw [Lagrange.interpolate_apply,eval_finsetSum]
  simp [basis]

theorem original {n:ℕ}(p:Polynomial ℂ)(size:p.natDegree ≤ n)(T q:ℂ)(inv:T*q=1):
    p.eval 1-p.eval 0=∑i:Fin (n+1),weight q i*p.eval (T*node i):=by
  let h:=p.comp (C T*X)
  have num:h.natDegree ≤ n:=by
    refine (natDegree_comp_le.trans ?_).trans size
    have d:(C T*X).natDegree ≤ 1:=(natDegree_mul_le.trans (by simp))
    exact (Nat.mul_le_mul_left _ d).trans_eq (Nat.mul_one _)
  have eq (z:ℂ):h.eval z=p.eval (T*z):=by simp [h,eval_comp]
  have a:=read h num q
  have b:=read h num 0
  simp only [eq,inv,mul_zero] at a b
  rw [a,b,←sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  unfold weight
  ring

def expense (p:Polynomial ℂ):ℝ:=∑i∈range (p.natDegree+1),‖p.coeff i‖
def price (n:ℕ):ℝ:=∑i:Fin (n+1),expense (basis i)

private theorem difference (p:Polynomial ℂ)(z:ℂ)(small:‖z‖ ≤ 1):
    ‖p.eval z-p.eval 0‖ ≤ ‖z‖*expense p:=by
  rw [eval_eq_sum_range,eval_eq_sum_range,←sum_sub_distrib]
  unfold expense
  rw [mul_sum]
  refine (norm_sum_le ..).trans (sum_le_sum ?_)
  intro i _
  cases i with
  | zero =>simp; positivity
  | succ i =>
    simp only [zero_pow (Nat.succ_ne_zero _),mul_zero,sub_zero,norm_mul,norm_pow]
    rw [mul_comm ‖z‖]
    exact mul_le_mul_of_nonneg_left (by
      rw [pow_succ]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) small)) (norm_nonneg _)

theorem earned (n:ℕ)(q:ℂ)(small:‖q‖ ≤ 1):
    ∑i:Fin (n+1),‖weight q i‖ ≤ ‖q‖*price n:=by
  unfold price
  rw [mul_sum]
  exact sum_le_sum fun i _=>difference (basis i) q small

end YM.Integration.WilsonOriginalOccupiedStencil
