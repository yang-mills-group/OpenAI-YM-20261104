import YM.Integration.WilsonRegisteredTwoPatchHaar

/-! An unnormalized rectangle identity for two local observations. Its
determinant keeps the sign of all four weights inside the same integral. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredRectangleMoment
open MeasureTheory RG WilsonCoeffUV WilsonCoeffUV.Bank.Mosaic
open scoped Classical
variable {X Y:Type*}[MeasurableSpace X][MeasurableSpace Y](μ:Measure X)(ν:Measure Y)
    [IsProbabilityMeasure μ][IsProbabilityMeasure ν]

def minor (p:X×Y→ℂ)(x y:X×Y):ℂ:=p x*p y-p (y.1,x.2)*p (x.1,y.2)

private theorem lift {A B:Type*}[MeasurableSpace A][MeasurableSpace B]{f:B→ℂ}(h:Envelope f)
    {g:A→B}(m:Measurable g):Envelope (fun a=>f (g a)):=by
  obtain ⟨c,cap⟩:=h.cost
  exact ⟨h.meas.comp m,c,fun a=>cap (g a)⟩

private theorem edge {p:X×Y→ℂ}(e:Envelope p):
    Envelope (fun x=>∫y,p (x,y) ∂ν) ∧ Envelope (fun y=>∫x,p (x,y) ∂μ):=by
  obtain ⟨c,cap⟩:=e.cost
  constructor
  · refine ⟨(e.meas.stronglyMeasurable.integral_prod_right' (ν:=ν)).measurable,c,fun x=>?_⟩
    simpa using norm_integral_le_of_norm_le_const (μ:=ν) (C:=c) (ae_of_all _ fun y=>cap (x,y))
  · refine ⟨((e.meas.comp measurable_swap).stronglyMeasurable.integral_prod_right' (ν:=μ)).measurable,c,fun y=>?_⟩
    simpa using norm_integral_le_of_norm_le_const (μ:=μ) (C:=c) (ae_of_all _ fun x=>cap (x,y))

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem point [IsFiniteMeasure μ][IsFiniteMeasure ν]{p:X×Y→ℂ}(ep:Envelope p)(x:X×Y):
    (∫y,minor p x y ∂μ.prod ν)=p x*(∫y,p y ∂μ.prod ν)-
      (∫a,p (a,x.2) ∂μ)*(∫b,p (x.1,b) ∂ν):=by
  let a(y:X):=p (y,x.2)
  let b(y:Y):=p (x.1,y)
  have ea:Envelope a:=lift ep (measurable_id.prodMk measurable_const)
  have eb:Envelope b:=lift ep (measurable_const.prodMk measurable_id)
  have first:Integrable (fun y=>p x*p y) (μ.prod ν):=(ep.integrableC _).const_mul _
  have last:Integrable (fun y:X×Y=>a y.1*b y.2) (μ.prod ν):=((lift ea measurable_fst).mulC (lift eb measurable_snd)).integrableC _
  unfold minor
  rw [integral_sub first last,integral_const_mul,integral_prod_mul (μ:=μ) (ν:=ν) a b]

theorem measured {p:X×Y→ℂ}(ep:Envelope p)(f:X→ℂ)(ef:Envelope f)(g:Y→ℂ)(eg:Envelope g):
    let ξ:=μ.prod ν
    (∫x,(f x.1*g x.2)*(∫y,minor p x y ∂ξ) ∂ξ)=
      (∫x,(f x.1*g x.2)*p x ∂ξ)*(∫x,p x ∂ξ)-
      (∫x,f x.1*p x ∂ξ)*(∫x,g x.2*p x ∂ξ):=by
  intro ξ
  let M:=∫x,p x ∂ξ
  let a(x:X):=∫y,p (x,y) ∂ν
  let b(y:Y):=∫x,p (x,y) ∂μ
  let F(x:X×Y):=f x.1*g x.2
  have eF:Envelope F:=(lift ef measurable_fst).mulC (lift eg measurable_snd)
  have ea:Envelope a:=(edge μ ν ep).1
  have eb:Envelope b:=(edge μ ν ep).2
  have lhs:∀x:X×Y,F x*(∫y,minor p x y ∂ξ)=
      (F x*p x)*M-(f x.1*a x.1)*(g x.2*b x.2):=by
    intro x
    rw [point μ ν ep x]
    dsimp [F,M,a,b,ξ];ring
  have ifp:Integrable (fun x:X×Y=>f x.1*p x) ξ:=((lift ef measurable_fst).mulC ep).integrableC _
  have igp:Integrable (fun x:X×Y=>g x.2*p x) ξ:=((lift eg measurable_snd).mulC ep).integrableC _
  have xf:(∫x,f x.1*p x ∂ξ)=∫x,f x*a x ∂μ:=by
    rw [integral_prod _ ifp]
    simp_rw [integral_const_mul];rfl
  have yg:(∫x,g x.2*p x ∂ξ)=∫y,g y*b y ∂ν:=by
    rw [integral_prod_symm _ igp]
    simp_rw [integral_const_mul];rfl
  have top:Integrable (fun x=>(F x*p x)*M) ξ:=((eF.mulC ep).integrableC ξ).mul_const M
  have side:Integrable (fun x:X×Y=>(f x.1*a x.1)*(g x.2*b x.2)) ξ:=
    ((lift (ef.mulC ea) measurable_fst).mulC (lift (eg.mulC eb) measurable_snd)).integrableC ξ
  change (∫x,F x*(∫y,minor p x y ∂ξ) ∂ξ)=_
  simp_rw [lhs]
  rw [integral_sub top side,integral_mul_const,integral_prod_mul (μ:=μ) (ν:=ν) (fun x=>f x*a x) (fun y=>g y*b y),xf,yg]
end YM.Integration.WilsonRegisteredRectangleMoment
