import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6PolynomialLaw

/-! The near energy on its genuine interacting patch, with its own
thermal-polynomial denominator. Its error is a signed scalar observable
suitable for the original centered exterior arms. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.F6Regular
open Function Filter Finset MeasureTheory Lattice RG YM.Wilson OPE.Therm Marked.Inherited RoseCut
open scoped Classical BigOperators
open private subenv from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6RegularCovariance
open private scalar_ratio from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6PolynomialLaw

private theorem pay_factor {X:Type*}[MeasurableSpace X](ν:Measure X)[IsProbabilityMeasure ν]
    (K f:X→ℝ)(ek:Envelope K)(ef:Envelope f)(M δ:ℝ)(bound:∀x,|f x|≤M)(dn:0≤δ)(ds:δ≤1/2)(dist:∀x,|K x-1|≤δ):
    let z:=∫x,K x ∂ν;let m:=∫x,f x ∂ν
    0<z ∧ |(∫x,K x*f x ∂ν)/z-m|≤4*M*δ:=by
  intro z m
  have one:Integrable (fun _:X=>(1:ℝ)) ν:=integrable_const _
  have d0:|z-1|≤δ:=by
    have e: (∫x,K x-1 ∂ν)=z-1:=by rw [integral_sub (ek.integrable ν) one];simp [z]
    rw [←e,←Real.norm_eq_abs];simpa only [probReal_univ,mul_one] using
      (norm_integral_le_of_norm_le_const (μ:=ν) (f:=fun x=>K x-1) (.of_forall fun x=>by simpa only [Real.norm_eq_abs] using dist x))
  have zpos:(1/2:ℝ)≤z:=by linarith only [(abs_le.mp d0).1,ds]
  have zp:0<z:=lt_of_lt_of_le (by norm_num) zpos
  have mn: |m|≤M:=by rw [←Real.norm_eq_abs];simpa only [probReal_univ,mul_one] using
    (norm_integral_le_of_norm_le_const (μ:=ν) (f:=f) (.of_forall fun x=>by simpa only [Real.norm_eq_abs] using bound x))
  have Mp:0≤M:=(abs_nonneg _).trans mn
  let F:=fun x=>f x-m
  have eF:Envelope F:=subenv ef (Envelope.const _)
  have eq:(∫x,(K x-1)*F x ∂ν)=(∫x,K x*f x ∂ν)-z*m:=by
    have p(x):(K x-1)*F x=K x*f x-K x*m-f x+m:=by dsimp only [F];ring
    have T:Integrable (fun x=>K x*f x-K x*m) ν:=((ek.mul ef).integrable ν).sub ((ek.integrable ν).mul_const m)
    have W:Integrable (fun x=>K x*f x-K x*m-f x) ν:=T.sub (ef.integrable ν)
    simp_rw [p]
    rw [integral_add W (integrable_const _),integral_sub T (ef.integrable ν),
      integral_sub ((ek.mul ef).integrable ν) ((ek.integrable ν).mul_const m),integral_mul_const,integral_const]
    simp only [probReal_univ,one_smul,z,m];ring
  have boost:|(∫x,K x*f x ∂ν)-z*m|≤δ*(2*M):=by
    rw [←eq,←Real.norm_eq_abs]
    have point(x):‖(K x-1)*F x‖≤δ*(2*M):=by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (dist x) ((abs_sub ..).trans ((add_le_add (bound x) mn).trans_eq (two_mul _).symm)) (abs_nonneg _) dn
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=ν) (.of_forall point)
  refine ⟨zp,?_⟩
  rw [show (∫x,K x*f x ∂ν)/z-m=((∫x,K x*f x ∂ν)-z*m)/z by field_simp,abs_div,abs_of_pos zp]
  apply (div_le_iff₀ zp).mpr;exact boost.trans (by nlinarith only [mul_le_mul_of_nonneg_left zpos (mul_nonneg (mul_nonneg (by norm_num : 0≤(4:ℝ)) Mp) dn)])

theorem scalar_thermal_quotient {X:Type*}[MeasurableSpace X](ν:Measure X)[IsProbabilityMeasure ν]
    (d f:X→ℝ)(de:Envelope d)(ef:Envelope f)(M ω:ℝ)(wn:0≤ω)(small:ω≤1/4)(band:∀x,|d x|≤ω)(fee:∀x,|f x|≤M)(k:ℕ):
    let K:=fun x=>Real.exp (d x)*tiltTaylor k (-d x)
    0<(∫x,K x ∂ν) ∧ |(∫x,K x*f x ∂ν)/(∫x,K x ∂ν)-(∫x,f x ∂ν)|≤8*M*ω^(k+1):=by
  intro K
  have pp:Continuous (tiltTaylor k):=by unfold tiltTaylor;fun_prop
  have km:Measurable K:= (Real.continuous_exp.measurable.comp de.meas).mul (pp.measurable.comp de.meas.neg)
  have sq:ω^(k+1)≤ω:=by rw [pow_succ];exact mul_le_of_le_one_left wn (pow_le_one₀ wn (small.trans (by norm_num)))
  have sm:2*ω^(k+1)≤1/2:=by linarith only [small,sq]
  have dist(x):|K x-1|≤2*ω^(k+1):=(scalar_ratio k (d x) ω small (band x)).2.2
  have ek:Envelope K:=⟨km,2,fun x=>by rw [Real.norm_eq_abs,abs_of_pos (scalar_ratio k (d x) ω small (band x)).1];linarith only [(abs_le.mp (dist x)).2,sm]⟩
  have ans:=pay_factor ν K f ek ef M (2*ω^(k+1)) fee (by positivity) sm dist
  exact ⟨ans.1,ans.2.trans_eq (by ring)⟩

end YM.Integration.FVA1Physical.Exchange.F6Regular
