import YM.Integration.WilsonRootedPosteriorDifferences

/-! The complex conditional mixed row and both singleton terms,
centered before the rooted matter variation is priced. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedPosteriorConnected
open Function Filter Finset MeasureTheory Lattice Wilson RG Supply Input Precision Marker Multi Exterior Tree
open Comparison.RG02 Actual
open WilsonRootedPosteriorDifferences (oscillation)
open scoped Topology BigOperators Classical
variable {X:Type*}[MeasurableSpace X](μ:Measure X)

def center (f:X→ℂ)(x:X):ℂ:=f x-∫v,f v ∂μ

def test (a b j:X→ℂ)(x:X):ℂ:=
  center μ j x-(∫v,b v ∂μ)*center μ a x-(∫v,a v ∂μ)*center μ b x

def variation (w:X→ℝ)(f:X→ℂ)(t:ℂ):ℂ:=∫x,Complex.exp (t*(w x:ℂ))*f x ∂μ

def response (w:X→ℝ)(a b j:X→ℂ)(t:ℂ):ℂ:=
  let e:=variation μ w
  e j t/e (fun _=>1) t-(e a t/e (fun _=>1) t)*(e b t/e (fun _=>1) t)

theorem centered_env (f:X→ℂ)(hf:Envelope f):Envelope (center μ f):=hf.subC (Envelope.constC _)

theorem test_env (a b j:X→ℂ)(ha:Envelope a)(hb:Envelope b)(hj:Envelope j):Envelope (test μ a b j):=
  ((centered_env μ j hj).subC ((Envelope.constC _).mulC (centered_env μ a ha))).subC
    ((Envelope.constC _).mulC (centered_env μ b hb))

theorem singleton [IsProbabilityMeasure μ](w f:X→ℂ)(hw:Envelope w)(hf:Envelope f):
    (∫x,w x*center μ f x ∂μ)=(∫x,w x*f x ∂μ)-(∫x,w x ∂μ)*(∫x,f x ∂μ):=by
  unfold center
  simp_rw [mul_sub]
  rw [integral_sub ((hw.mulC hf).integrableC μ) ((hw.integrableC μ).mul_const _),integral_mul_const]

theorem original [IsProbabilityMeasure μ](w a b j:X→ℂ)(hw:Envelope w)(ha:Envelope a)(hb:Envelope b)(hj:Envelope j):
    (∫x,w x*test μ a b j x ∂μ)=
      (∫x,w x*j x ∂μ)-((∫x,w x ∂μ)*(∫x,j x ∂μ)+(∫x,w x*a x ∂μ)*(∫x,b x ∂μ)+
        (∫x,w x*b x ∂μ)*(∫x,a x ∂μ))+2*(∫x,w x ∂μ)*(∫x,a x ∂μ)*(∫x,b x ∂μ):=by
  let u:=∫x,a x ∂μ
  let v:=∫x,b x ∂μ
  have geom (x:X):w x*test μ a b j x=w x*center μ j x-v*(w x*center μ a x)-u*(w x*center μ b x):=by
    unfold test
    dsimp only [u,v]
    ring
  have ca:Integrable (fun x=>w x*center μ a x) μ:=(hw.mulC (centered_env μ a ha)).integrableC μ
  have cb:Integrable (fun x=>w x*center μ b x) μ:=(hw.mulC (centered_env μ b hb)).integrableC μ
  have cj:Integrable (fun x=>w x*center μ j x) μ:=(hw.mulC (centered_env μ j hj)).integrableC μ
  have ha':Integrable (fun x=>w x*center μ j x-v*(w x*center μ a x)) μ:=cj.sub (ca.const_mul _)
  simp_rw [geom]
  erw [integral_sub ha' (cb.const_mul _),integral_sub cj (ca.const_mul _)]
  simp only [integral_const_mul,singleton μ w j hw hj,singleton μ w a hw ha,singleton μ w b hw hb,u,v]
  ring

theorem vanishes [IsProbabilityMeasure μ](a b j:X→ℂ)(ha:Envelope a)(hb:Envelope b)(hj:Envelope j):
    (∫x,test μ a b j x ∂μ)=0:=by
  have fromOne:=original μ (fun _=>1) a b j (Envelope.constC _) ha hb hj
  simp only [one_mul,integral_const,probReal_univ,one_smul] at fromOne
  rw [fromOne]
  ring

theorem subtract [IsProbabilityMeasure μ](w a b j:X→ℂ)(hw:Envelope w)(ha:Envelope a)(hb:Envelope b)(hj:Envelope j)(s:ℂ):
    (∫x,(w x-s)*test μ a b j x ∂μ)=∫x,w x*test μ a b j x ∂μ:=by
  have t:=test_env μ a b j ha hb hj
  simp_rw [sub_mul]
  rw [integral_sub ((hw.mulC t).integrableC μ) ((t.integrableC μ).const_mul _),integral_const_mul,vanishes μ a b j ha hb hj,mul_zero,sub_zero]

theorem copies [IsProbabilityMeasure μ](w a b j:X→ℂ)(hw:Envelope w)(ha:Envelope a)(hb:Envelope b)(hj:Envelope j):
    oscillation μ w (test μ a b j)=2*∫x,w x*test μ a b j x ∂μ:=by
  rw [WilsonRootedPosteriorDifferences.centered μ w _ hw (test_env μ a b j ha hb hj),vanishes μ a b j ha hb hj,mul_zero,sub_zero]

theorem sweep [IsProbabilityMeasure μ](w:X→ℝ)(a b j:X→ℂ)(hw:Envelope w)(ha:Envelope a)(hb:Envelope b)(hj:Envelope j):
    HasDerivAt (response μ w a b j) (∫x,(w x:ℂ)*test μ a b j x ∂μ) 0:=by
  have one:Envelope (fun _:X=>(1:ℂ)):=Envelope.constC _
  have d (f:X→ℂ)(paid:Envelope f):HasDerivAt (variation μ w f) (∫x,(w x:ℂ)*f x ∂μ) 0:=
    WilsonRootedNonflatExponential.integral w hw f (paid.integrableC μ)
  have zero (f:X→ℂ):variation μ w f 0=∫x,f x ∂μ:=by simp [variation]
  have norm:variation μ w (fun _=>1) 0=1:=by simp [zero]
  have step:=WilsonRootedNonflatExponential.pair (d _ one) (d a ha) (d b hb) (d j hj) (norm.trans_ne one_ne_zero)
  rw [norm,zero j,zero a,zero b] at step
  simp only [mul_one,div_one,one_pow] at step
  rw [original μ (fun x=>(w x:ℂ)) a b j hw.ofReal_env ha hb hj]
  exact step

end YM.Integration.WilsonRootedPosteriorConnected
