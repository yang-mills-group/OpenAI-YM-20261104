import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalPrior

/-! The exterior constant cancels between the actual numerator and the actual
partition function. The remaining insertion is the centered signed earlier action. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open OriginalMarkedRowCovariance WilsonHeldRetainedAction OriginalMarkedConditionalAction
open WilsonCoeffUV WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open scoped Classical BigOperators
variable {G:Gauge}

private theorem paid_mass {X:Type*}[MeasurableSpace X](μ:Measure X)[IsProbabilityMeasure μ]
    {p:X→ℝ}(ep:Envelope p)(positive:∀u,0<p u):0<∫u,p u ∂μ:=by
  apply (integral_pos_iff_support_of_nonneg (fun u=>(positive u).le) (ep.integrable μ)).2
  rw [show Function.support p=Set.univ from Set.eq_univ_of_forall fun u=>(positive u).ne'];simp

private theorem paid_scalar {X:Type*}[MeasurableSpace X](μ:Measure X)(c:ℝ)(hc:0<c)(z:X→ℝ)
    (hp:0<∫u,z u ∂μ)(F:X→ℂ):((∫u,z u ∂μ:ℝ):ℂ)*read μ (fun u=>c*z u) F=∫u,(z u:ℂ)*F u ∂μ:=by
  unfold OriginalMarkedRowCovariance.read
  simp_rw [Complex.ofReal_mul,mul_assoc,integral_const_mul]
  rw [Complex.ofReal_mul,mul_inv_rev]
  field_simp [Complex.ofReal_ne_zero.mpr hc.ne',Complex.ofReal_ne_zero.mpr hp.ne']

theorem spring_prior_exact (R:Run G){m N per r:ℕ}(live:m+1≤N){Z:SeriesA G}{σ C ε:ℝ}
    (osc:LocalSpringOscillation R m N per r Z σ C ε)
    (S:Support (R.family.side (m+1) per))(ext:Config G (R.family.side (m+1) per))
    (W:Config G (R.family.side m per)):
    let ξ:=OriginalMarkedConditionalAction.patch S ext
    let μ:=reference R N per m S ext W
    let ν:=springLocalPrior R m N per S ext W
    let h:=springLocalChange R m N per r Z σ C S ext
    let z (u):=Real.exp (h u)
    let p:=∫u,z u ∂ν
    0<p ∧ ∀F:Config G (R.family.side (m+1) per)→ℂ,
      reading R N per m S ext W (R.family.path.rep N per (m+1)) F=(∫u,F (ξ u) ∂ν) ∧
      (p:ℂ)*read μ (fun u=>maskedSpringWeight R (N:=N) r Z σ C (ξ u)) (fun u=>F (ξ u))=
      ∫u,(z u:ℂ)*F (ξ u) ∂ν:=by
  intro ξ μ ν h z p
  let y (u):=(R.family.path.rep N per (m+1)).eval (ξ u)
  let d:=maskedSpringScore R N per (m+1) r Z σ C
  let c:=Real.exp (d ext)
  letI:IsProbabilityMeasure μ:=probability R N per m S ext W
  letI:IsProbabilityMeasure ν:=(spring_prior_first R live osc S ext W).1
  have old:=RG02.Actual.eval_envelope R.makes.wilson (p:=per) live
  obtain ⟨T,rent⟩:=old.cost
  have ey:Envelope y:=⟨old.meas.comp (measurable_patch S ext),T,fun u=>rent _⟩
  have py (u):0<y u:=Multi.AxisShift.chosen_positive R.makes.wilson live (ξ u)
  have ready:=spring_prior_bounds R osc S ext
  have mz:Measurable z:=Real.measurable_exp.comp ready.1
  have ez:Envelope z:=⟨mz,Real.exp (ε*S.card*(regulatorRun R.family N per (m+1))^2/(2*Real.exp 2)),fun u=>by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr ((le_abs_self (h u)).trans (ready.2 u))⟩
  have pos:0<p:=paid_mass ν ez (fun _=>Real.exp_pos _)
  refine ⟨pos,?_⟩
  intro F
  constructor
  · change read μ y (fun u=>F (ξ u)) = ∫u,F (ξ u) ∂SignedWeightedMoment.normalized μ y
    simpa only [OriginalMarkedRowCovariance.read,Complex.real_smul,Complex.ofReal_inv] using
      (SignedWeightedMoment.normalized_integral μ ey.meas (fun u=>(py u).le) (paid_mass μ ey py) (fun u=>F (ξ u))).symm
  have native:(fun u=>maskedSpringWeight R (N:=N) r Z σ C (ξ u))=y*(fun u=>c*z u):=by
    funext u
    rw [spring_tilt]
    change Real.exp (d (ξ u))*y u=y u*(Real.exp (d ext)*Real.exp (d (ξ u)-d ext))
    rw [←Real.exp_add,show d ext+(d (ξ u)-d ext)=d (ξ u) by ring,mul_comm]
  rw [native,spring_read_twice μ ey.meas (fun u=>(py u).le) (paid_mass μ ey py)]
  exact paid_scalar ν c (Real.exp_pos _) z pos (fun u=>F (ξ u))

end YM.Integration.OriginalMarkedRunAction
