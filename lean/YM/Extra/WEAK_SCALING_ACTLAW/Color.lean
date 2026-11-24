import YM.Gauge.Colors
import YM.Gauge.Lie

set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling.Color
open Filter Set Function Gauge
open NormedSpace
open scoped Matrix.Norms.Frobenius Topology InnerProductSpace
variable {G: Gauge}
theorem tangent (x y : G.Color) : HasDerivAt (fun t : ℝ => G.adjoint (G.lieExp (t • x)) y) (G.ad x y) 0 := by
  let u := fun t : ℝ => exp (t • G.colorMat x)
  have he : HasDerivAt u (G.colorMat x) 0 := by simpa [u] using! hasDerivAt_exp_smul_const (G.colorMat x) (0:ℝ)
  have hf := (he.mul_const (G.colorMat y)).mul he.star
  have h : HasDerivAt (fun t : ℝ => G.colorMat (G.adjoint (G.lieExp (t • x)) y)) (G.colorMat (G.ad x y)) 0 := by
    simpa [u,Gauge.conjugate,map_smul, colorMat_skew,sub_eq_add_neg] using! hf
  have ht := G.projectColor.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0:ℝ) h
  change HasDerivAt (fun t : ℝ => G.projectColor (G.colorMat _)) (G.projectColor (G.colorMat _)) _ at ht
  simpa only [G.project_colorMat] using! ht
end YM.Extra.WeakScaling.Color
