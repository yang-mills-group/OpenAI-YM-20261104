import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskBoard
import YM.Integration.WilsonRootedInteriorRenderedWeight

/-! The whole signed spring, with all its actual indexed supports, in the
reference density carrying the original compatible forced activities. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson Comparison.RG02 OPE.Therm
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic IterationFour IterationFour.Vacuum
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonRootedInteriorPhysicalExponent
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {N per j:ℕ}
local notation "P" => R.family.path.rep N per j
local notation "g" => regulatorRun R.family N per j

def maskedSpringWeight (r:ℕ) (Z:SeriesA G) (σ C:ℝ) (U:Config G (R.family.side j per)) : ℝ :=
  let T:=∑x:Site (R.family.side j per),maskedSpringAt R N per j r Z σ C g x U
  Real.exp ((P).scalar-((P).path.inChannels (P).clip (P).p (R.family.path.β N per j) U+T))*
    (P).activities.gas (P).p U

private theorem ratio (p b h A E:ℝ) (z:ℝ) :
    Real.exp ((A-z)+E)*(Real.exp (b-(p+z))*h)⁻¹=h⁻¹*Real.exp (A+E-b+p) := by
  rw [mul_inv_rev,←Real.exp_neg]
  calc _=h⁻¹*(Real.exp ((A-z)+E)*Real.exp (-(b-(p+z)))):=by ring
       _=_:=by rw [←Real.exp_add];congr 2;ring

theorem masked_spring_ratio (r:ℕ) (Z:SeriesA G) (σ C:ℝ) (U:Config G (R.family.side j per))
    (L:List (Piece G (R.family.side j per))) (kept omitted:ℝ) :
    let T:=∑x:Site (R.family.side j per),maskedSpringAt R N per j r Z σ C g x U
    Real.exp ((kept-Render.renders (Render.prefactor g) (P).p U L)+omitted)*
      (renderedWeight R (N:=N) L U)⁻¹=
    Real.exp ((kept-T)+omitted)*(maskedSpringWeight R (N:=N) r Z σ C U)⁻¹ := by
  intro T
  unfold maskedSpringWeight renderedWeight
  exact (ratio _ _ _ kept omitted _).trans (ratio _ _ _ kept omitted T).symm

end YM.Integration.OriginalMarkedRunAction
