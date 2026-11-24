import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalDensity
import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalControl

/-! A correlated observable on the original local prior may be unbounded.
Its genuine first moment under that physical prior is the only test charge. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OriginalMarkedRowCovariance
open WilsonCoeffUV WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open scoped Classical BigOperators
variable {G:Gauge}

private theorem prior_mass {X:Type*}[MeasurableSpace X](μ:Measure X)[IsProbabilityMeasure μ]
    {k:X→ℝ}(ek:Envelope k)(pk:∀u,0<k u):0<∫u,k u ∂μ:=by
  apply (integral_pos_iff_support_of_nonneg (fun u=>(pk u).le) (ek.integrable μ)).2
  rw [show Function.support k=Set.univ from Set.eq_univ_of_forall fun u=>(pk u).ne'];simp

private theorem rescale {X:Type*}[MeasurableSpace X](μ:Measure X)(c:ℝ)(hc:c≠0)
    (k:X→ℝ)(f:X→ℂ)(mass:0<∫u,k u ∂μ):read μ (fun u=>c*k u) f=read μ k f:=by
  have h (u:X):((c*k u:ℝ):ℂ)*f u=(c:ℂ)*((k u:ℂ)*f u):=by rw [Complex.ofReal_mul,mul_assoc]
  unfold OriginalMarkedRowCovariance.read
  simp_rw [h]
  rw [integral_const_mul,integral_const_mul,Complex.ofReal_mul,mul_inv_rev]
  field_simp [Complex.ofReal_ne_zero.mpr hc,Complex.ofReal_ne_zero.mpr mass.ne']

theorem spring_physical_first (R:Run G){N per j:ℕ}(live:j≤N)(r:ℕ)(Z:SeriesA G)(σ C:ℝ)
    {X:Type*}[MeasurableSpace X](μ:Measure X)[IsProbabilityMeasure μ]
    (ξ:X → Config G (R.family.side j per))(mx:Measurable ξ)(exterior:Config G (R.family.side j per))
    (borel:Measurable (maskedSpringScore R N per j r Z σ C))(a:ℝ)
    (bound:∀u,|maskedSpringScore R N per j r Z σ C (ξ u)-maskedSpringScore R N per j r Z σ C exterior|≤a):
    let y (u:X):=(R.family.path.rep N per j).eval (ξ u)
    let ν:=SignedWeightedMoment.normalized μ y
    IsProbabilityMeasure ν ∧ ∀(F:X→ℂ),Integrable F ν→
    ‖read μ (fun u=>maskedSpringWeight R (N:=N) r Z σ C (ξ u)) F-read μ y F‖≤
      2*Real.exp (2*a)*a*∫u,‖F u‖ ∂ν:=by
  intro y ν
  let d:=maskedSpringScore R N per j r Z σ C
  let c:=Real.exp (d exterior)
  let z (u:X):=Real.exp (d (ξ u)-d exterior)
  have py (u:X):0<y u:=Multi.AxisShift.chosen_positive R.makes.wilson live (ξ u)
  have old:=RG02.Actual.eval_envelope R.makes.wilson (p:=per) live
  obtain ⟨T,rent⟩:=old.cost
  have ey:Envelope y:=⟨old.meas.comp mx,T,fun u=>rent _⟩
  have pay:=prior_mass μ ey py
  letI:IsProbabilityMeasure ν:=SignedWeightedMoment.mass_one μ ey (fun u=>(py u).le) pay
  have positive (u:X):0<z u:=Real.exp_pos _
  have lower (u:X):Real.exp (-a)≤z u:=Real.exp_le_exp.mpr (abs_le.mp (bound u)).1
  have upper (u:X):z u≤Real.exp a:=Real.exp_le_exp.mpr (abs_le.mp (bound u)).2
  have measured:Measurable z:=Real.measurable_exp.comp ((borel.comp mx).sub measurable_const)
  have ez:Envelope z:=⟨measured,Real.exp a,fun u=>(Real.norm_of_nonneg (positive u).le).trans_le (upper u)⟩
  have native:(fun u:X=>maskedSpringWeight R (N:=N) r Z σ C (ξ u))=y*(fun u=>c*z u):=by
    funext u
    rw [spring_tilt]
    change Real.exp (d (ξ u))*y u=y u*(c*z u)
    rw [show c*z u=Real.exp (d exterior+(d (ξ u)-d exterior)) from (Real.exp_add ..).symm]
    rw [show d exterior+(d (ξ u)-d exterior)=d (ξ u) by ring,mul_comm]
  refine ⟨inferInstance,?_⟩
  intro F hf
  have base:read μ y F=∫u,F u ∂ν:=by
    simpa only [OriginalMarkedRowCovariance.read,Complex.real_smul,Complex.ofReal_inv] using
      (SignedWeightedMoment.normalized_integral μ ey.meas (fun u=>(py u).le) pay F).symm
  rw [base,native,spring_read_twice μ ey.meas (fun u=>(py u).le) pay,
    rescale ν c (Real.exp_pos _).ne' z F (prior_mass ν ez positive)]
  exact spring_tilt_first ν z measured a lower upper F hf

end YM.Integration.OriginalMarkedRunAction
