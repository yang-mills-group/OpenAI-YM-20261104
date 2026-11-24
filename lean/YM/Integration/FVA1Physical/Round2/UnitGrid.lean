import YM.Integration.FVA1Physical.Round2.SummableReset
import YM.Ac.Tree
import YM.Push.ABSOLUTE_SUMS.Basic

/-! Recover homogeneous Wilson coefficients at the full field using probes
within the same field ball. The finite interpolation charge depends only on
the requested polynomial degree, independently of period and field dimension. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Finset MvPolynomial MSbar MSbar.Rolling MSbar.Bakery MSbar.Cacao MSbar.Wave MSbar.Bakery.Portal
open scoped BigOperators Classical
variable {σ : Type} [Fintype σ]

def unitGrid (n : ℕ) (j : Fin (n+1)) : ℝ := (j.val:ℝ)/((n:ℝ)+1)

theorem unitGrid_mem (n : ℕ) (j : Fin (n+1)) : unitGrid n j ∈ Set.Icc (0:ℝ) 1 := by
  have hd : 0<(n:ℝ)+1 := by positivity
  refine ⟨div_nonneg (Nat.cast_nonneg _) hd.le,(div_le_one hd).mpr ?_⟩
  exact_mod_cast j.isLt.le

def gridCoeff (n : ℕ) (i j : Fin (n+1)) : ℝ := (Matrix.vandermonde (unitGrid n))⁻¹ i j

def gridPrice (n : ℕ) (i : Fin (n+1)) : ℝ := ∑ j, |gridCoeff n i j|

theorem unitGrid_row (n : ℕ) (P : Pot σ) (deg : P.totalDegree ≤ n) (x : View σ) (i : Fin (n+1)) :
    eval x (homogeneousComponent i.val P) = ∑ j, gridCoeff n i j * eval (unitGrid n j • x) P := by
  let M := Matrix.vandermonde (unitGrid n)
  have hd : IsUnit M.det := by
    rw [isUnit_iff_ne_zero,Matrix.det_vandermonde_ne_zero_iff]
    intro j k eqn
    have h : (j.val:ℝ)/((n:ℝ)+1) = (k.val:ℝ)/((n:ℝ)+1) := eqn
    have ne : (n:ℝ)+1 ≠ 0 := by positivity
    have := (div_left_inj' ne).mp h
    apply Fin.ext
    exact_mod_cast this
  let v (j : Fin (n+1)) := eval x (homogeneousComponent j.val P)
  have val (j : Fin (n+1)) : eval (unitGrid n j • x) P = ∑ k, M j k * v k := by
    change _ = ∑ k : Fin (n+1), unitGrid n j ^ k.val * eval x (homogeneousComponent k.val P)
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => unitGrid n j ^ k * eval x (homogeneousComponent k P)) (n+1)]
    calc
      _ = eval (unitGrid n j • x) (∑ k∈range (n+1),homogeneousComponent k P) :=
        congrArg (fun Q : Pot σ => eval (unitGrid n j • x) Q) (buys n P deg).symm
      _ = _ := by rw [map_sum]; exact sum_congr rfl fun k _=> hene (unitGrid n j) (unitGrid n j) x k P
  simp_rw [val]
  change v i = ∑ j,M⁻¹ i j * ∑ k,M j k * v k
  simp only [mul_sum,←mul_assoc]
  rw [sum_comm]
  simp only [←sum_mul,←Matrix.mul_apply,Matrix.nonsing_inv_mul M hd]
  simp [Matrix.one_apply]

theorem unitGrid_price (n : ℕ) (P : Pot σ) (deg : P.totalDegree ≤ n) (x : View σ)
    (i : Fin (n+1)) {w : ℝ} (cap : ∀ j, |eval (unitGrid n j • x) P| ≤ w) :
    |eval x (homogeneousComponent i.val P)| ≤ gridPrice n i * w := by
  rw [unitGrid_row n P deg x i]
  calc
    _ ≤ ∑ j, |gridCoeff n i j * eval (unitGrid n j • x) P| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |gridCoeff n i j| * w := sum_le_sum fun j _=> by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (cap j) (abs_nonneg _)
    _ = _ := (sum_mul ..).symm

/- A different coarse field may be probed at each address. The same local
coefficient majorant still pays the complete exponential support weight. -/
theorem unitGrid_hit {ι : Type} {c : Lattice.Side} (X : ι→Lattice.Support c) (B n : ℕ)
    (a price : ℝ) (P : ι→Pot σ) (deg : ∀ l,(P l).totalDegree ≤ n)
    (mass : ι→ℝ) (original : Ac.Hit X B mass a price)
    (x : ι→View σ) (cap : ∀ l j, |eval (unitGrid n j • x l) (P l)| ≤ mass l)
    (i : Fin (n+1)) :
    Ac.Hit X B (fun l => |eval (x l) (homogeneousComponent i.val (P l))|) a (gridPrice n i*price) := by
  intro z
  have nn : 0 ≤ gridPrice n i := sum_nonneg fun j _=>abs_nonneg _
  apply Push.AbsoluteSums.budget_mono (Push.AbsoluteSums.budget_scale nn (original z))
  · intro l; split <;> positivity
  intro l
  by_cases hl : z∈X l
  · simp only [if_pos hl]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (unitGrid_price n _ (deg l) (x l) i (cap l)) (Real.exp_nonneg _)
  · simp [hl]
end YM.Integration.FVA1Physical.Round2
