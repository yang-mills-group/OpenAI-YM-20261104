import YM.Integration.WilsonRootedInteriorPhysicalExponent

/-! The rendered reference keeps the original complete gas at the same physical configuration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedInteriorPhysicalExponent
open Lattice Wilson RG Marker PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric LocalComparison
variable {G : Gauge} (R : Run G) {N per j : ℕ}
local notation "X" => R.family.path.rep N per j
local notation "g" => Pert.Asymptotics.regulatorRun R.family N per j

/-- Evaluate the selected rendered layers with the full original forced gas. -/
def renderedWeight (L : List (Piece G (R.family.side j per))) (U : Config G (R.family.side j per)) : ℝ :=
  Real.exp ((X).scalar-((X).path.inChannels (X).clip (X).p (R.family.path.β N per j) U+
    Render.renders (Render.prefactor (g)) (X).p U L)) * (X).activities.gas (X).p U

theorem rendered_inverse (L : List (Piece G (R.family.side j per))) (U : Config G (R.family.side j per)) :
    ((X).eval U)⁻¹ = Real.exp (discrepancy R (N:=N) L U) * (renderedWeight R (N:=N) L U)⁻¹ := by
  have factor : (X).eval U = (Real.exp (discrepancy R (N:=N) L U))⁻¹ * renderedWeight R (N:=N) L U := by
    rw [density R L U]
    unfold renderedWeight
    rw [Real.exp_sub,div_eq_mul_inv]
    ring
  rw [factor,mul_inv_rev,inv_inv,mul_comm]

end YM.Integration.WilsonRootedInteriorPhysicalExponent
