import YM.Integration.WilsonPosteriorProjectionPolarization

/-! Only the finitely many selected wire slots enter the coarse chart room
and the true angular bill, even when the side length grows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionWireRoom
open Finset Set Lattice Wilson RG Precision Tree Exterior Push.Uniform
open WilsonPosteriorProjectionRay WilsonPosteriorProjectionWire
open scoped BigOperators Classical
variable {G : Gauge} {c : Side} {r : ℕ}

def slots (u : Fin r → ℝ) := ∑ j, |u j|

theorem blend_as_coordinates (v : Fin r → Letter G c) (u : Fin r → ℝ) :
    studio v u = ∑ j, u j • Pi.single (((v j).1,(v j).2.1),(v j).2.2) (1 : ℝ) := by
  change photograph (blend v u) = _
  simp only [blend,LinearMap.sum_apply,LinearMap.smulRight_apply,LinearMap.proj_apply,map_sum,map_smul]
  apply sum_congr rfl
  intro j _
  rw [show photograph (impulse (v j)) = _ from chart_letter (v j)]

theorem room (v : Fin r → Letter G c) (u : Fin r → ℝ) (g s : ℝ) :
    ‖g • (s • studio v u)‖ ≤ |g| * |s| * slots u := by
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  rw [blend_as_coordinates]
  exact (norm_sum_le ..).trans_eq (by simp only [slots,norm_smul,Pi.norm_single,norm_one,
    mul_one,Real.norm_eq_abs])

end YM.Integration.WilsonPosteriorProjectionWireRoom

