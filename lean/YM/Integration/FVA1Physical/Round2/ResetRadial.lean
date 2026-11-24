import YM.Integration.FVA1Physical.Round2.ResetCatalogue
import Mathlib.LinearAlgebra.Vandermonde

/-! Radial evaluation of a bounded-degree Wilson coefficient determines its
homogeneous rows. This finite interpolation also applies to summable regular
and forced presentations, using the same independently chosen coarse field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Finset MvPolynomial MSbar MSbar.Rolling MSbar.Bakery MSbar.Cacao MSbar.Wave MSbar.Bakery.Portal
open scoped BigOperators Classical
variable {σ α : Type} [Fintype σ]

private def radialGrid {n : ℕ} (j : Fin (n+1)) : ℝ := j.val

private theorem radial_extract {n : ℕ} (a : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    ∑ j, (Matrix.vandermonde (@radialGrid n))⁻¹ i j *
      (∑ k, radialGrid j ^ k.val * a k) = a i := by
  let M := Matrix.vandermonde (@radialGrid n)
  have hd : IsUnit M.det := by
    rw [isUnit_iff_ne_zero,Matrix.det_vandermonde_ne_zero_iff]
    intro j k h
    apply Fin.ext
    exact_mod_cast (show (j.val : ℝ) = k.val from h)
  have hM := Matrix.nonsing_inv_mul M hd
  change ∑ j, M⁻¹ i j * (∑ k, M j k * a k) = a i
  simp only [mul_sum,←mul_assoc]
  rw [sum_comm]
  simp only [←sum_mul,←Matrix.mul_apply,hM]
  simp [Matrix.one_apply]

private theorem radial_eval (n : ℕ) (P : Pot σ) (hP : P.totalDegree ≤ n)
    (x : View σ) (t : ℝ) :
    eval (t • x) P = ∑ k : Fin (n+1), t^k.val * eval x (homogeneousComponent k.val P) := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => t^k * eval x (homogeneousComponent k P)) (n+1)]
  calc
    _ = eval (t • x) (∑ k∈range (n+1), homogeneousComponent k P) :=
      congrArg (fun F : Pot σ => eval (t • x) F) (buys n P hP).symm
    _ = _ := by rw [map_sum]; exact sum_congr rfl fun k _ => hene t t x k P

private theorem radial_row (n : ℕ) (P : Pot σ) (hP : P.totalDegree ≤ n)
    (x : View σ) (i : Fin (n+1)) :
    ∑ j, (Matrix.vandermonde (@radialGrid n))⁻¹ i j * eval (radialGrid j • x) P =
      eval x (homogeneousComponent i.val P) := by
  simp_rw [radial_eval n P hP x]
  exact radial_extract _ i

/-- The same finite bank of scalar tests extracts each component even when
the represented catalogue is infinite. Only convergence of the evaluated
incoming readings and the independently checkable polynomial degree enter. -/
theorem radial_hasSum {n : ℕ} (P : α → Pot σ) (T : Pot σ) (x : View σ)
    (hP : ∀ a, (P a).totalDegree ≤ n) (hT : T.totalDegree ≤ n)
    (h : ∀ j : Fin (n+1), HasSum (fun a => eval ((j.val : ℝ) • x) (P a))
        (eval ((j.val : ℝ) • x) T)) (i : Fin (n+1)) :
    HasSum (fun a => eval x (homogeneousComponent i.val (P a)))
      (eval x (homogeneousComponent i.val T)) := by
  let M := Matrix.vandermonde (@radialGrid n)
  have rows (j : Fin (n+1)) :
      HasSum (fun a => M⁻¹ i j * eval (radialGrid j • x) (P a))
        (M⁻¹ i j * eval (radialGrid j • x) T) := (h j).mul_left _
  rw [←radial_row n T hT x i]
  exact (hasSum_sum (s:=univ) (fun j _ => rows j)).congr_fun
    (fun a => (radial_row n (P a) (hP a) x i).symm)
end YM.Integration.FVA1Physical.Round2
