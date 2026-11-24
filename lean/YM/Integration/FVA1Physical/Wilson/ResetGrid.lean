import YM.Integration.FVA1Physical.Round2.UnitGrid
import YM.Comparison.RG02.Adjacent.Rank

/-! A measured inverse coupling/field reset samples only points in the
original field ball. Its error on polynomial marked rows is controlled by
a dimension- and period-independent finite interpolation charge. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Finset Analysis Comparison.RG02 Comparison.RG02.Valence Comparison.RG02.Adjacent
open PertExtension.Series Comparison.RG02.Moving.Path FVA1Physical.Round2
open scoped Classical BigOperators ContDiff
variable {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem grid_jet {f:X→ℂ} {n:ℕ} (hf:Level (n:ℤ) f) (x:X) (i:Fin (n+1)) :
    Assembly.jet f i.val x = ∑ j, (gridCoeff n i j:ℂ)*f (unitGrid n j • x) := by
  let M := Matrix.vandermonde (unitGrid n)
  have invert : IsUnit M.det := by
    rw [isUnit_iff_ne_zero,Matrix.det_vandermonde_ne_zero_iff]
    intro j k e
    have eq : (j.val:ℝ)/((n:ℝ)+1) = (k.val:ℝ)/((n:ℝ)+1) := e
    apply Fin.ext
    exact_mod_cast (div_left_inj' (show (n:ℝ)+1≠0 by positivity)).mp eq
  let v (k:Fin (n+1)) := Assembly.jet f k.val x
  have nodes (j:Fin (n+1)) : f (unitGrid n j • x) = ∑ k, ((M j k:ℝ):ℂ)*v k := by
    rw [hf.posted]
    change _ = ∑ k:Fin (n+1), ((unitGrid n j ^ k.val:ℝ):ℂ)*Assembly.jet f k.val x
    rw [Fin.sum_univ_eq_sum_range (fun k:ℕ=> ((unitGrid n j ^ k:ℝ):ℂ)*Assembly.jet f k x) (n+1)]
    apply sum_congr rfl
    intro k _
    rw [Assembly.Clipper.weight,Complex.real_smul]
  simp_rw [nodes]
  change v i = ∑ j, ((M⁻¹ i j:ℝ):ℂ) * ∑ k, ((M j k:ℝ):ℂ)*v k
  simp only [mul_sum,←mul_assoc,←Complex.ofReal_mul]
  rw [sum_comm]
  simp only [←sum_mul,←Complex.ofReal_sum,←Matrix.mul_apply,Matrix.nonsing_inv_mul M invert]
  simp only [Matrix.one_apply]
  rw [sum_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · simp

theorem grid_jet_error {f h:X→ℂ} {n:ℕ} (hf:Level (n:ℤ) f) (hh:Level (n:ℤ) h)
    (x:X) (i:Fin (n+1)) {δ:ℝ} (cap:∀ j,‖f (unitGrid n j • x) - h (unitGrid n j • x)‖ ≤ δ) :
    ‖Assembly.jet f i.val x - Assembly.jet h i.val x‖ ≤ gridPrice n i * δ := by
  rw [grid_jet hf,grid_jet hh,←sum_sub_distrib]
  simp_rw [←mul_sub]
  refine (norm_sum_le ..).trans ?_
  calc
    _ ≤ ∑ j:Fin (n+1), |gridCoeff n i j| * δ := sum_le_sum fun j _=>by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (cap j) (abs_nonneg _)
    _ = gridPrice n i*δ := (sum_mul ..).symm

end YM.Integration.FVA1Physical.Wilson
