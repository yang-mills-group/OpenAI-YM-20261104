import YM.Integration.WilsonPositionProgramTrialTorusDifferences
import YM.Pert.Fourier.Band

/-! The native mean-zero Wilson Green line has a uniform polynomial finite-side
price. A first difference removes the constant forcing away from its two poles. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialTorusLine
open Finset Lattice Pert Pert.Orb Pert.Full
open WilsonPositionProgramTrialTorusDifferences (jet)
open scoped BigOperators Classical
variable {n : Side}

theorem mesh_bound {p : Site n} (hp : p≠0) : mesh n ≤ ‖moment p‖ := by
  have ne : lift p ≠ 0 := by
    intro zero
    exact hp (by rw [←wrap_lift p,zero,map_zero])
  obtain ⟨i,hi⟩ : ∃i, lift p i ≠ 0 := by
    by_contra! h
    exact ne (funext h)
  have one : (1:ℝ) ≤ |(lift p i : ℝ)| := by
    have ab : (0 : ℤ) < |lift p i| := abs_pos.mpr hi
    exact_mod_cast (by omega : (1:ℤ) ≤ |lift p i|)
  have h := Band.coordinate_le (moment p) i
  rw [moment_apply,abs_mul,abs_of_pos mesh_pos] at h
  exact (le_mul_of_one_le_right mesh_pos.le one).trans h

theorem price (p : Site n) : (delta (moment p))⁻¹ ≤ (n.val : ℝ)^2 := by
  by_cases zero : p = 0
  · subst p
    simp [delta,moment,incVec,Lattice.lift]
  have h := (sq_le_sq₀ mesh_pos.le (norm_nonneg _)).mpr (mesh_bound (n:=n) zero)
  have factor := mul_le_mul_of_nonneg_right (h.trans (delta_bound (moment_cube p))) (sq_nonneg (n.val : ℝ))
  have normal : (mesh n)^2*(n.val : ℝ)^2=4*Real.pi^2 := by rw [←mul_pow,mesh_val]; ring
  rw [normal] at factor
  have comparison : (16:ℝ) ≤ (n.val:ℝ)^2*delta (moment p) := by
    apply le_of_mul_le_mul_left (a:=(Real.pi^2)/4) _ (by positivity)
    nlinarith only [factor]
  rw [←one_div,div_le_iff₀ (delta_pos (moment_cube p) (moment_ne zero))]
  linarith

theorem original (x : Site n) : |(toroid x).re| ≤ (n.val : ℝ)^2 := by
  rw [toroid_real]
  have nf : 0 ≤ (n.val : ℝ)^(-4:ℤ) := by positivity
  calc
    _ ≤ ∑ p : Site n, |(n.val : ℝ)^(-4:ℤ) * (delta (moment p))⁻¹ * Real.cos (corner (lift x) (moment p))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Site n, (n.val : ℝ)^(-4:ℤ)*(n.val : ℝ)^2 := by
      apply sum_le_sum
      intro p _
      have dp : 0 ≤ delta (moment p) := sum_nonneg (fun _ _ => by positivity)
      rw [abs_mul,abs_mul,abs_of_nonneg nf,abs_of_nonneg (inv_nonneg.mpr dp)]
      exact (mul_le_of_le_one_right (mul_nonneg nf (inv_nonneg.mpr dp)) (abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)).trans
        (mul_le_mul_of_nonneg_left (price p) nf)
    _ = _ := by
      simp only [sum_const,card_univ,site_card,nsmul_eq_mul,Nat.cast_pow,zpow_neg]
      field_simp

def green (x : Site n) : ℝ := (toroid x).re

theorem harmonic (i : Axis) (x : Site n) (left : x ≠ 0) (right : x+step i ≠ 0) :
    lap (ahead i green) x = 0 := by
  rw [WilsonPositionProgramTrialTorusDifferences.commute]
  change lap (fun y : Site n => (toroid y).re) (x+step i) - lap (fun y : Site n => (toroid y).re) x = 0
  rw [lap_shift,lap_shift,if_neg left,if_neg right,sub_self]

end YM.Integration.WilsonPositionProgramTrialTorusLine
