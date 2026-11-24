import YM.Pert.Fourier.Source

/-! Local energy of the scalar periodic Green line in the actual based
Feynman gauge. The constant Fourier forcing is retained until a first
difference of the line is taken. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialTorusEnergy
open Finset Lattice Pert.Orb
open scoped BigOperators Classical
variable {n : Side}

theorem axis (u χ : Site n → ℝ) (i : Axis) :
    (∑ x, (ahead i (χ*u) x)^2) +
    (∑ x, (χ x)^2 * u x * past i (ahead i u) x) =
    ∑ x, (ahead i χ x)^2 * u x * u (x+step i) := by
  let v := fun x => (χ x)^2*u x
  have edge : (∑ x, ahead i v x * ahead i u x) =
      -(∑ x, v x * past i (ahead i u) x) := by
    simpa only [P,Real.inner_apply,mul_comm] using ahead_adjoint v (ahead i u) i
  change _ + (∑ x, v x * _) = _
  calc
    _ = (∑ x, (ahead i (χ*u) x)^2) - ∑ x, ahead i v x * ahead i u x := by
      linarith only [edge]
    _ = _ := by
      rw [←sum_sub_distrib]
      apply sum_congr rfl
      intro x _
      dsimp [ahead,v]
      ring

theorem energy (u χ : Site n → ℝ) :
    (∑ i : Axis, ∑ x, (ahead i (χ*u) x)^2) +
    (∑ x, (χ x)^2 * u x * lap u x) =
    ∑ i : Axis, ∑ x, (ahead i χ x)^2 * u x * u (x+step i) := by
  simp only [lap_expand,mul_sum]
  rw [sum_comm (s := univ) (t := (univ : Finset Axis)), ←sum_add_distrib]
  exact sum_congr rfl (fun i _ => axis u χ i)

theorem harmonic (u χ : Site n → ℝ) (locality : ∀ x, χ x ≠ 0 → lap u x = 0) :
    (∑ i : Axis, ∑ x, (ahead i (χ*u) x)^2) =
    ∑ i : Axis, ∑ x, (ahead i χ x)^2 * u x * u (x+step i) := by
  have vanished : (∑ x, (χ x)^2*u x*lap u x)=0 := by
    apply sum_eq_zero
    intro x _
    by_cases active : χ x = 0
    · simp [active]
    · rw [locality x active,mul_zero]
  simpa only [vanished,add_zero] using energy u χ

end YM.Integration.WilsonPositionProgramTrialTorusEnergy
