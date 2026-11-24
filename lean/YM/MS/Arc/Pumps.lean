import YM.MS.Arc.Leaves

set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real
open scoped Topology Interval
variable {E F G: Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F] [NormedAddCommGroup G] [NormedSpace ℝ G]
def ups (S:ℂ): Prop := 0<2*S.re+1
-- differs from actual dr by β = π^z /Γ(z+1) times measure factor. n-dim ordinary outputs then β.
def gage (m:ℕ): ℝ:= π⁻¹^m *2*(-(2:ℝ)⁻¹)^(m+1)
variable [MeasurableSpace G] [BorelSpace G] [FiniteDimensional ℝ G] (μ:Measure G) [μ.IsAddHaarMeasure]
def carpet (μ:Measure G)(f:(G×ℝ)×E→ F): Tree E F:= fun p=> ∫ x,f ((x,p.1),p.2) ∂μ
end YM.MS.Arc
