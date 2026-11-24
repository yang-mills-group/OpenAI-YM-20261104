import YM.Integration.WilsonCoherentPivotStencil
import Mathlib.LinearAlgebra.Lagrange

/-! Real probes on one original curvature stencil.  The interpolation price depends
on the field degree and the radial scale alone. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFirstReceivedRadialStencil
open Finset Polynomial Function Lattice Wilson RG
open RGComparison.Core16 RGComparison.Core16.Spool
open scoped Classical BigOperators

def node (d j : ℕ) : ℝ := (j:ℝ)/(d+1:ℕ)

theorem node_mem {d j : ℕ} (hj : j≤d) : node d j ∈ Set.Icc (0:ℝ) 1 := by
  refine ⟨div_nonneg (by positivity) (by positivity), ?_⟩
  change (j:ℝ)/(d+1:ℕ) ≤ 1
  apply (div_le_one (by positivity)).2
  exact_mod_cast Nat.le_succ_of_le hj

private def nodes (d j : ℕ) : ℂ := node d j

def budget (d : ℕ) : ℝ := ∑ k∈range (d+1),∑ j∈range (d+1),
  ‖(Lagrange.basis (range (d+1)) (nodes d) j).coeff k‖

theorem priced (P : Polynomial ℂ) {d : ℕ} (deg : P.natDegree≤d) {A : ℝ}
    (samples : ∀j≤d,‖P.eval (node d j:ℂ)‖≤A) (x : ℝ) :
    ‖P.eval (x:ℂ)‖≤A*budget d*(1+|x|)^d := by
  have inj : Set.InjOn (nodes d) (range (d+1)) := by
    intro i _ j _ h
    have hij : node d i=node d j := Complex.ofReal_injective h
    exact_mod_cast (div_left_inj' (by positivity : (d+1:ℕ)≠(0:ℝ))).mp hij
  have degree_bound : P.degree < ((range (d+1)).card : WithBot ℕ) :=
    P.degree_le_natDegree.trans_lt (by
      rw [card_range]
      exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le deg))
  have rep := Lagrange.eq_interpolate (s:=range (d+1)) (v:=nodes d) (f:=P) inj degree_bound
  have coeff (k : ℕ) : ‖P.coeff k‖≤A*∑ j∈range (d+1),
        ‖(Lagrange.basis (range (d+1)) (nodes d) j).coeff k‖ := by
    conv_lhs => rw [rep,Lagrange.interpolate_apply,Polynomial.finsetSum_coeff]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro j hj
    rw [Polynomial.coeff_C_mul,norm_mul]
    exact mul_le_mul_of_nonneg_right (samples j (Nat.le_of_lt_succ (mem_range.mp hj))) (norm_nonneg _)
  have total : ∑ k∈range (d+1), ‖P.coeff k‖≤A*budget d := by
    rw [budget,Finset.mul_sum]
    exact sum_le_sum (fun k _=>coeff k)
  have one : 1≤1+|x| := by linarith [abs_nonneg x]
  have point : ‖(x:ℂ)‖≤1+|x| := by rw [Complex.norm_real,Real.norm_eq_abs];linarith
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le deg)]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ k∈range (d+1),‖P.coeff k‖*(1+|x|)^d := by
      apply sum_le_sum
      intro k hk
      rw [norm_mul,norm_pow]
      exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (norm_nonneg _) point k).trans
        (pow_le_pow_right₀ one (Nat.le_of_lt_succ (mem_range.mp hk)))) (norm_nonneg _)
    _ ≤ A*budget d*(1+|x|)^d := by
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right total (pow_nonneg (zero_le_one.trans one) d)

variable {G : Gauge} {I : Type} [Fintype I] (J : I→Lamp G)
local notation "L" => Slice J

def polynomial (b:L→G.El) (z:L→G.Color) (d:ℕ) (g:ℝ) : Polynomial ℂ :=
  ∑ j∈range (d+1), Polynomial.monomial j
    ((g:ℂ)^j * SignedChartTaylor.jet (WilsonCoherentPivotStencil.field J b) z j)

theorem degree (b:L→G.El) (z:L→G.Color) (d:ℕ) (g:ℝ) :
    (polynomial J b z d g).natDegree≤d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact (Polynomial.natDegree_monomial_le ..).trans (Nat.le_of_lt_succ (mem_range.mp hj))

theorem evaluation (b:L→G.El) (z:L→G.Color) (d:ℕ) (g x:ℝ) :
    (polynomial J b z d g).eval (x:ℂ)=WilsonCoherentPivotStencil.row J b z d (g*x) := by
  unfold polynomial WilsonCoherentPivotStencil.row
  simp only [Polynomial.eval_finsetSum,Polynomial.eval_monomial,Complex.real_smul,
    Complex.ofReal_pow,Complex.ofReal_mul,mul_pow]
  apply sum_congr rfl
  intro j _
  ring

end YM.Integration.WilsonFirstReceivedRadialStencil
