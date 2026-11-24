import YM.Integration.WilsonEmittedSignedTariff
/-! Only the original external Laurent pole and the single stage wage
enter the group-field reservation for a finite-period jet discrepancy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedWindingGroupFare
open Lattice Wilson RG Push Push.Local QuadraticLocal Comparison.Density.Mirrors
open WilsonEmittedSignedTariff
variable {n:Side}

def fee (T:ℕ) : ℝ := boxCost*((2*T:ℕ):ℝ)*((3*T:ℕ):ℝ)

theorem original (B:BudgetPoint) (y:Site n) (T q pole:ℕ) {g δ mass:ℝ}
    (hg:0 < g) (hδ:0 ≤ δ) (cap:B.supportExponent+2 ≤ 102)
    (seam:δ ≤ g^(q+3+pole+1)*mass) :
    reservedMass B (neighborhood (B.B+1) y)
      (‖(↑((g^pole)⁻¹):ℂ)‖*(g⁻¹*((2*T:ℕ):ℝ)*((3*T:ℕ):ℝ)*δ)) ≤
      fee T*mass*g^(q+3) := by
  have box:=WilsonEmittedShortTariff.tax B y cap
  have realnorm:‖(↑((g^pole)⁻¹):ℂ)‖=(g^pole)⁻¹:=by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hg.le _))]
  have refunded:(g^pole)⁻¹*(g⁻¹*((2*T:ℕ):ℝ)*((3*T:ℕ):ℝ)*δ) ≤
      ((2*T:ℕ):ℝ)*((3*T:ℕ):ℝ)*mass*g^(q+3):=by
    calc
      _ ≤ (g^pole)⁻¹*(g⁻¹*((2*T:ℕ):ℝ)*((3*T:ℕ):ℝ)*(g^(q+3+pole+1)*mass)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left seam (by positivity)) (by positivity)
      _ = _:=by rw [pow_succ,pow_add];field_simp
  unfold reservedMass fee
  rw [realnorm]
  calc
    _ ≤ boxCost*(((2*T:ℕ):ℝ)*((3*T:ℕ):ℝ)*mass*g^(q+3)) :=
      mul_le_mul box refunded (by positivity) (Real.exp_pos _).le
    _ = _:=by ring

end YM.Integration.WilsonEmittedWindingGroupFare
