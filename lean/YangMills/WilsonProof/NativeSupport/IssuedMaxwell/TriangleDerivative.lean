import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.TriangleLines
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedMaxwell.TriangleDerivative
open YM YM.XSpace YM.Maxwell MeasureTheory
open scoped ContDiff

theorem original (a:ℝ)(ha:a≠0)(i:Axis)(f:E4→ℝ)(x:E4):
    grad i (fun u=>a*f u) x = a*grad i f x:=by
  change (fderiv ℝ (a • f) x) (basis i)= a*((fderiv ℝ f x) (basis i))
  by_cases h:DifferentiableAt ℝ f x
  · rw [fderiv_const_smul h];rfl
  · have hh:¬DifferentiableAt ℝ (a • f) x:=by
      intro hh
      have good:=hh.const_smul a⁻¹
      apply h
      simpa only [smul_smul,inv_mul_cancel₀ ha,one_smul] using good
    rw [fderiv_zero_of_not_differentiableAt hh,fderiv_zero_of_not_differentiableAt h]
    simp
end IssuedMaxwell.TriangleDerivative
end
