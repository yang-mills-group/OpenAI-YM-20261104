import YM.Integration.WilsonHeldRetainedAction

/-! Cancelling the common positive Haar normalization preserves the complete
old physical density inside the marked numerator. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredExteriorNormalization
open MeasureTheory RG OriginalMarkedRowCovariance
open scoped Classical
variable {X:Type*}[MeasurableSpace X]

private theorem scalar {x:ℂ}(hx:x≠0)(y z:ℂ):(x*y)⁻¹*(x*z)=y⁻¹*z:=by
  calc
    _=y⁻¹*(x⁻¹*x)*z:=by rw [mul_inv_rev];ring
    _=_:=by simp [hx]

theorem scaled (μ:Measure X)(k:X→ℝ)(f:X→ℂ){t:ℝ}(ht:t≠0):
    read μ (fun u=>t*k u) f=read μ k f:=by
  unfold OriginalMarkedRowCovariance.read
  simp only [Complex.ofReal_mul,mul_assoc,integral_const_mul]
  exact scalar (by exact_mod_cast ht) ..

theorem weighted (μ:Measure X)(k p:X→ℝ)(f:X→ℂ)(mk:Measurable k)(kp:∀x,0≤k x)
    (hc:0<∫u,k u ∂μ):
    read (SignedWeightedMoment.normalized μ k) p f=read μ (fun u=>k u*p u) f:=by
  unfold OriginalMarkedRowCovariance.read
  rw [SignedWeightedMoment.normalized_integral μ mk kp hc p,
    SignedWeightedMoment.normalized_integral μ mk kp hc (fun u=>(p u:ℂ)*f u)]
  simp only [smul_eq_mul,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_inv,mul_assoc]
  exact scalar (inv_ne_zero (by exact_mod_cast hc.ne')) ..
end YM.Integration.WilsonRegisteredExteriorNormalization
