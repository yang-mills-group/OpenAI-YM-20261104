import YM.Integration.WilsonRootedNonflatIncome

/-! One actual exponential variation of a bounded signed scalar in the
original interacting numerator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedNonflatExponential
open Function Filter MeasureTheory Lattice Wilson RG Supply Input Precision Marker Multi Exterior Tree
open Comparison.RG02 Actual
open scoped Topology BigOperators
variable {X:Type*}[MeasurableSpace X]{μ:Measure X}

theorem integral (w:X→ℝ)(hw:Envelope w)(u:X→ℂ)(hu:Integrable u μ):
    HasDerivAt (fun t:ℂ=>∫x,Complex.exp (t*(w x:ℂ))*u x ∂μ) (∫x,(w x:ℂ)*u x ∂μ) 0:=by
  let M:=max 0 hw.cost.choose
  have bound (x:X):‖w x‖≤M:=(hw.cost.choose_spec x).trans (le_max_right ..)
  let F:=fun (t:ℂ)(x:X)=>Complex.exp (t*(w x:ℂ))*u x
  let D:=fun (t:ℂ)(x:X)=>Complex.exp (t*(w x:ℂ))*(w x:ℂ)*u x
  have wm:Measurable (fun x=>(w x:ℂ)):=Complex.continuous_ofReal.measurable.comp hw.1
  have em (t:ℂ):Measurable (fun x=>Complex.exp (t*(w x:ℂ))):=
    Complex.continuous_exp.measurable.comp (measurable_const.mul wm)
  have cm (t:ℂ):AEStronglyMeasurable (F t) μ:=(em t).aestronglyMeasurable.mul hu.aestronglyMeasurable
  have dm:AEStronglyMeasurable (D 0) μ:=((em 0).mul wm).aestronglyMeasurable.mul hu.aestronglyMeasurable
  have at0:Integrable (F 0) μ:=by simpa [F] using hu
  have cap:Integrable (fun x=>Real.exp M*M*‖u x‖) μ:=hu.norm.const_mul _
  have size (x:X)(t:ℂ)(ht:t∈Metric.ball 0 1):‖D t x‖≤Real.exp M*M*‖u x‖:=by
    have small:‖t‖<1:=by simpa only [Metric.mem_ball,dist_zero_right] using ht
    have e:‖Complex.exp (t*(w x:ℂ))‖≤Real.exp M:=by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      calc
        _≤‖t*(w x:ℂ)‖:=Complex.re_le_norm _
        _=‖t‖*‖w x‖:=by rw [norm_mul,Complex.norm_real]
        _≤1*M:=mul_le_mul small.le (bound x) (norm_nonneg _) zero_le_one
        _=M:=one_mul _
    simp only [D,norm_mul,Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (mul_le_mul e (bound x) (norm_nonneg _) (Real.exp_pos _).le) (norm_nonneg _)
  have term (x:X)(t:ℂ):HasDerivAt (fun s=>F s x) (D t x) t:=by
    simpa +instances only [F,D,id_eq,one_mul,Function.comp_apply] using (((Complex.hasDerivAt_exp _).comp t ((hasDerivAt_id t).mul_const (w x:ℂ))).mul_const (u x))
  have h:HasDerivAt (fun t=>∫x,F t x ∂μ) (∫x,D 0 x ∂μ) 0:=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=F) (F':=D) (μ:=μ)
      (Metric.ball_mem_nhds 0 zero_lt_one) (Eventually.of_forall cm) at0 dm
      (bound:=fun x=>Real.exp M*M*‖u x‖) (ae_of_all _ size) cap (ae_of_all _ (fun x t _=>term x t))).2
  simpa only [D,F,zero_mul,Complex.exp_zero,one_mul] using h

variable {G:Gauge}{c f:Side}{S:StepData c f}{β:ℝ}

theorem pushed (kernel:S.IsKernel β G)(V:Config G c)(w:Config G f→ℝ)(hw:Envelope w)
    (u:Config G f→ℂ)(hu:Envelope u):
    HasDerivAt (fun t:ℂ=>S.push β (fun U=>Complex.exp (t*(w U:ℂ))*u U) V)
      (S.push β (fun U=>(w U:ℂ)*u U) V) 0:=by
  have m:=StepData.push_slice kernel V u (hu.integrableC _)
  have d:=integral w hw (fun U=>S.density β U V • u U) m
  simpa only [StepData.push,Complex.real_smul,mul_left_comm] using d

theorem pair {q a b j:ℂ→ℂ}{dq da db dj:ℂ}
    (hq:HasDerivAt q dq 0)(ha:HasDerivAt a da 0)(hb:HasDerivAt b db 0)(hj:HasDerivAt j dj 0)(nz:q 0≠0):
    HasDerivAt (fun t=>j t/q t-(a t/q t)*(b t/q t))
      (dj/q 0-(dq*j 0+da*b 0+db*a 0)/(q 0)^2+2*dq*a 0*b 0/(q 0)^3) 0:=by
  have h:HasDerivAt (fun t=>j t/q t-(a t/q t)*(b t/q t))
      ((dj*q 0-j 0*dq)/(q 0)^2-((da*q 0-a 0*dq)/(q 0)^2*(b 0/q 0)+
        (a 0/q 0)*((db*q 0-b 0*dq)/(q 0)^2))) 0:=
    (hj.div hq nz).sub ((ha.div hq nz).mul (hb.div hq nz))
  have eq:dj/q 0-(dq*j 0+da*b 0+db*a 0)/(q 0)^2+2*dq*a 0*b 0/(q 0)^3=
      (dj*q 0-j 0*dq)/(q 0)^2-((da*q 0-a 0*dq)/(q 0)^2*(b 0/q 0)+
        (a 0/q 0)*((db*q 0-b 0*dq)/(q 0)^2)):=by
    field_simp
    ring
  rw [eq]
  exact h

end YM.Integration.WilsonRootedNonflatExponential
