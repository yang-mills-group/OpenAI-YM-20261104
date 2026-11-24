import YM.Integration.SignedWeightedMoment
import YM.Integration.OriginalMarkedRowPrice

/-! The normalized change of density on the original probability space.
Only the previous physical first moment of the joint test is charged. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open MeasureTheory Function OriginalMarkedRowCovariance
open scoped Classical
variable {X:Type*}[MeasurableSpace X]

theorem spring_read_twice (μ:Measure X){k:X→ℝ}(meas:Measurable k)(nonneg:∀u,0≤k u)
    (mass:0<∫u,k u ∂μ)(z:X→ℝ)(F:X→ℂ):
    read μ (k*z) F=read (SignedWeightedMoment.normalized μ k) z F:=by
  let P:=∫u,k u ∂μ
  let Q:=∫u,k u*z u ∂μ
  let b:=∫u,(k u:ℂ)*((z u:ℂ)*F u) ∂μ
  rw [OriginalMarkedRowCovariance.read,OriginalMarkedRowCovariance.read,
    SignedWeightedMoment.normalized_integral μ meas nonneg mass z,
    SignedWeightedMoment.normalized_integral μ meas nonneg mass (fun u=>(z u:ℂ)*F u)]
  simp only [Pi.mul_apply,Complex.ofReal_mul,Complex.real_smul,smul_eq_mul,mul_assoc]
  change (Q:ℂ)⁻¹*b=(((P⁻¹:ℝ):ℂ)*(Q:ℂ))⁻¹*(((P⁻¹:ℝ):ℂ)*b)
  have pp:(P:ℂ)≠0:=Complex.ofReal_ne_zero.mpr mass.ne'
  simp only [Complex.ofReal_inv,mul_inv_rev,inv_inv]
  field_simp [pp]

private theorem spring_relative_span (a z m:ℝ)(lo:Real.exp (-a)≤z)(hi:z≤Real.exp a)
    (low:Real.exp (-a)≤ m)(high:m≤Real.exp a):
    |z/m-1|≤2*Real.exp (2*a)*a:=by
  have mp:0 < m:=(Real.exp_pos _).trans_le low
  have span:|z-m|≤Real.exp a-Real.exp (-a):=abs_le.mpr ⟨by linarith,by linarith⟩
  have spread:Real.exp a-Real.exp (-a)≤2*a*Real.exp a:=by
    have step:=mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-2*a)) (Real.exp_pos a).le
    rw [←Real.exp_add,show a+-2*a= -a by ring] at step
    linarith
  have back:m⁻¹≤Real.exp a:=by
    rw [Real.exp_neg] at low
    calc m⁻¹ ≤ ((Real.exp a)⁻¹)⁻¹ := (inv_le_inv₀ mp (inv_pos.mpr (Real.exp_pos a))).2 low
         _=Real.exp a := inv_inv _
  rw [show z/m-1=(z-m)*m⁻¹ by field_simp [mp.ne'],abs_mul,abs_of_pos (inv_pos.mpr mp)]
  calc _≤(2*a*Real.exp a)*Real.exp a:=mul_le_mul (span.trans spread) back (inv_pos.mpr mp).le
        ((abs_nonneg _).trans (span.trans spread))
       _=2*Real.exp (2*a)*a:=by rw [show 2*a=a+a by ring,Real.exp_add];ring

theorem spring_tilt_first (μ:Measure X)[IsProbabilityMeasure μ](z:X→ℝ)(mz:Measurable z)
    (a:ℝ)(lo:∀u,Real.exp (-a)≤z u)(hi:∀u,z u≤Real.exp a)(F:X→ℂ)(hf:Integrable F μ):
    ‖read μ z F-∫u,F u ∂μ‖≤2*Real.exp (2*a)*a*∫u,‖F u‖ ∂μ:=by
  let m:=∫u,z u ∂μ
  have positive (u:X):0<z u:=(Real.exp_pos _).trans_le (lo u)
  have ez:RG.Envelope z:=⟨mz,Real.exp a,fun u=>(Real.norm_of_nonneg (positive u).le).trans_le (hi u)⟩
  have low:Real.exp (-a)≤ m:=by simpa using integral_mono (integrable_const (μ:=μ) (Real.exp (-a))) (ez.integrable μ) lo
  have high:m≤Real.exp a:=by simpa using integral_mono (ez.integrable μ) (integrable_const (μ:=μ) (Real.exp a)) hi
  have zf:Integrable (fun u=>(z u:ℂ)*F u) μ:=by
    apply (hf.norm.const_mul (Real.exp a)).mono' ((Complex.continuous_ofReal.measurable.comp mz).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun u=>by
      change ‖(z u:ℂ)*F u‖ ≤ _
      simpa only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (positive u).le] using mul_le_mul_of_nonneg_right (hi u) (norm_nonneg (F u))
  let Δ (u:X):=(((z u/m-1:ℝ):ℂ))*F u
  have same:read μ z F-(∫u,F u ∂μ)=∫u,Δ u ∂μ:=by
    have h (u:X):Δ u=(m:ℂ)⁻¹*((z u:ℂ)*F u)-F u:=by
      simp only [Δ,div_eq_mul_inv,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_one];ring
    simp_rw [h]
    rw [integral_sub (zf.const_mul _) hf,integral_const_mul]
    rfl
  rw [same,←integral_const_mul]
  apply norm_integral_le_of_norm_le (hf.norm.const_mul _)
  exact Filter.Eventually.of_forall fun u=>by
    simpa only [Δ,norm_mul,Complex.norm_real,Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right (spring_relative_span a (z u) m (lo u) (hi u) low high) (norm_nonneg (F u))

end YM.Integration.OriginalMarkedRunAction
