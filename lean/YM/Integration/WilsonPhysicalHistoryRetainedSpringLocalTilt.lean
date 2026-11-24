import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalCourse
import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskWeight
import YM.Integration.OriginalMarkedConditionalAction

/-! Normalize the physical and independently filed masked actions on the
same conditional sample, with the unchanged full forced gas in both. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson MeasureTheory
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OriginalMarkedRowCovariance
open scoped Classical BigOperators
variable {G:Gauge}

theorem spring_tilt (R:Run G) {N per j:ℕ} (r:ℕ)(Z:SeriesA G)(σ C:ℝ)
    (U:Config G (R.family.side j per)):
    maskedSpringWeight R (N:=N) r Z σ C U=Real.exp (maskedSpringScore R N per j r Z σ C U)*
      (R.family.path.rep N per j).eval U:=by
  change Real.exp (_-(_+_))*_=Real.exp (_-_)*(Real.exp (_-_-_)*_)
  rw [←mul_assoc,←Real.exp_add]
  congr 2
  simp only [Rep.scalar]
  ring

private theorem posIntegral {X:Type*} [MeasurableSpace X] (μ:Measure X) [IsProbabilityMeasure μ]
    {k:X→ℝ}(e:Envelope k)(pos:∀u,0<k u):0<∫u,k u ∂μ:=by
  apply (integral_pos_iff_support_of_nonneg (fun u=>(pos u).le) (e.integrable μ)).2
  rw [show Function.support k=Set.univ from Set.eq_univ_of_forall fun u=>(pos u).ne']
  simp

private theorem scale_read {X:Type*}[MeasurableSpace X](μ:Measure X)(c:ℝ)(hc:c≠0)
    (k:X→ℝ)(f:X→ℂ)(hk:0<∫u,k u ∂μ):read μ (fun u=>c*k u) f=read μ k f:=by
  have linear:(∫u,((c*k u:ℝ):ℂ)*f u ∂μ)=(c:ℂ)*∫u,(k u:ℂ)*f u ∂μ:=by
    simp only [Complex.ofReal_mul,mul_assoc];exact integral_const_mul ..
  unfold OriginalMarkedRowCovariance.read
  rw [linear,integral_const_mul,Complex.ofReal_mul]
  field_simp [Complex.ofReal_ne_zero.mpr hc,Complex.ofReal_ne_zero.mpr hk.ne']

theorem spring_fiber (R:Run G) {N per j:ℕ}(live:j≤N)(r:ℕ)(Z:SeriesA G)(σ C:ℝ)
    {X:Type*}[MeasurableSpace X][Nonempty X](μ:Measure X)[IsProbabilityMeasure μ]
    (ξ:X → Config G (R.family.side j per))(mx:Measurable ξ)(exterior:Config G (R.family.side j per))
    (borel:Measurable (maskedSpringScore R N per j r Z σ C))(a:ℝ)
    (bound:∀u,|maskedSpringScore R N per j r Z σ C (ξ u)-maskedSpringScore R N per j r Z σ C exterior|≤a)
    (F:X→ℂ)(meas:Measurable F)(B:ℝ)(hb:0≤B)(cap:∀u,‖F u‖≤B):
    ‖read μ (fun u=>maskedSpringWeight R (N:=N) r Z σ C (ξ u)) F-
      read μ (fun u=>(R.family.path.rep N per j).eval (ξ u)) F‖≤2*Real.exp (2*a)*a*B:=by
  let v (u:X):=(R.family.path.rep N per j).eval (ξ u)
  let d:=maskedSpringScore R N per j r Z σ C
  let c:=Real.exp (d exterior)
  let k (u:X):=c*v u
  let z (u:X):=Real.exp (d (ξ u)-d exterior)
  have old:=RG02.Actual.eval_envelope R.makes.wilson (p:=per) live
  obtain ⟨T,price⟩:=old.cost
  have ev:Envelope v:=⟨old.meas.comp mx,T,fun u=>price (ξ u)⟩
  have pv (u:X):0<v u:=Multi.AxisShift.chosen_positive R.makes.wilson live (ξ u)
  have ek:Envelope k:=(Envelope.const c).mul ev
  have pk (u:X):0<k u:=mul_pos (Real.exp_pos _) (pv u)
  have ha:0≤a:=(abs_nonneg _).trans (bound (Classical.choice (inferInstance:Nonempty X)))
  have measured:Measurable z:=Real.measurable_exp.comp ((borel.comp mx).sub measurable_const)
  have lower (u:X):Real.exp (-a)≤z u:=Real.exp_le_exp.mpr (abs_le.mp (bound u)).1
  have upper (u:X):z u≤Real.exp a:=Real.exp_le_exp.mpr (abs_le.mp (bound u)).2
  have native:(fun u:X=>maskedSpringWeight R (N:=N) r Z σ C (ξ u))=k*z:=by
    funext u
    rw [spring_tilt]
    change Real.exp (d (ξ u))*v u=(c*v u)*z u
    have exact_weight:c*z u=Real.exp (d (ξ u)):=by
      rw [show c*z u=Real.exp (d exterior+(d (ξ u)-d exterior)) from (Real.exp_add ..).symm]
      congr 1;ring
    rw [←exact_weight];ring
  have paid:=OriginalMarkedRowPrice.normalized_tilt μ ek (fun u=>(pk u).le)
    (posIntegral μ ek pk) measured a ha lower upper F meas B hb cap
  rw [native,←scale_read μ c (Real.exp_pos _).ne' v F (posIntegral μ ev pv)]
  exact paid

end YM.Integration.OriginalMarkedRunAction
