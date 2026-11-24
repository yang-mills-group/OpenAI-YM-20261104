import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionNormalizedConnected

/-! Keep all seven proper readings in a single signed influence observable
when changing the vacuum in a connected three-field measurement. Its lower
rows retain their two original, generally different, finite-volume means. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset MeasureTheory RG Matrix
open scoped Classical BigOperators
open private fibre_prob fibre_reading from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionNormalizedConnected
variable {X:Type*}[MeasurableSpace X]

/-- Ordered as A,B,C,AB,AC,BC,ABC. -/
def properThree (u:Fin 7→ℂ):ℂ := u 6-u 3*u 2-u 4*u 1-u 5*u 0+2*u 0*u 1*u 2

def properWeights (u v:Fin 7→ℂ):Fin 7→ℂ:=
  ![-v 5+2*u 1*u 2,-v 4+2*v 0*u 2,-v 3+2*v 0*v 1,-u 2,-u 1,-u 0,1]

theorem signed_proper_weights (u v:Fin 7→ℂ):
    properThree u-properThree v=∑i:Fin 7, properWeights u v i*(u i-v i):=by
  simp [properThree,properWeights,Fin.sum_univ_succ]
  ring

private theorem complex_gift {F:X→ℂ}(e:Envelope F)(μ:Measure X)[IsFiniteMeasure μ]:Integrable F μ:=by
  obtain ⟨M,hm⟩:=e.cost
  exact Integrable.of_bound e.meas.aestronglyMeasurable M (.of_forall hm)

private theorem linear_mean {ι:Type}[Fintype ι] (μ:Measure X) {u:X→ℝ}
    (um:Measurable u)(ui:Integrable u μ)(un:∀x,0≤u x)(up:0<∫x,u x ∂μ)
    (w:ι→ℂ)(F:ι→X→ℂ)(e:∀i,Envelope (F i)):
    FrozenRead.meanOn μ u (fun x=>∑i:ι,w i*F i x)=∑i:ι,w i*FrozenRead.meanOn μ u (F i):=by
  let ν:=fibreLaw μ u
  letI:=fibre_prob μ ui un up
  have pay (i:ι):Integrable (fun x=>w i*F i x) ν := (complex_gift (e i) ν).const_mul _
  rw [←fibre_reading μ um un up]
  change (∫x,∑i:ι,w i*F i x ∂ν)=_
  rw [integral_finsetSum univ (fun i _=>pay i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul]
  exact congrArg (w i * ·) (fibre_reading μ um un up (F i))

/-- Exactly one action oscillation is tested. For projected raw products
take F=(A,B,C,AB,AC,BC,ABC), with one product *before* either integration.
This algebra also applies to independently smeared, jointly rooted test
functions carried on one common field. -/
theorem seven_signed_action (μ:Measure X)[SFinite μ] {k a b r:X→ℝ}
    (km:Measurable k)(am:Measurable a)(bm:Measurable b)(kn:∀x,0≤k x)
    (ap:∀x,0<a x)(bp:∀x,0<b x)(rm:Measurable r)(anchor:ℝ)
    (same:∀x,Real.log (a x)-Real.log (b x)=r x+anchor)
    (F:Fin 7→X→ℂ)(e:∀i,Envelope (F i)):
    let u:=fun x=>k x*a x;let v:=fun x=>k x*b x
    let U:=fun i=>FrozenRead.meanOn μ u (F i);let V:=fun i=>FrozenRead.meanOn μ v (F i)
    let J:=fun x=>∑i:Fin 7,properWeights U V i*F i x
    let z:=∫x,u x ∂μ;let q:=∫x,v x ∂μ
    Integrable u μ → Integrable v μ → 0<z → 0<q →
      (properThree U-properThree V=FrozenRead.meanOn μ u J-FrozenRead.meanOn μ v J) ∧
      2*z*q*‖properThree U-properThree V‖≤
       ∫t,Replica.actionBill u v r t*‖J t.1-J t.2‖ ∂μ.prod μ:=by
  intro u v U V J z q ui vi zp qp
  let w:=properWeights U V
  have uj:=linear_mean μ (km.mul am) ui (fun x=>mul_nonneg (kn x) (ap x).le) zp w F e
  have vj:=linear_mean μ (km.mul bm) vi (fun x=>mul_nonneg (kn x) (bp x).le) qp w F e
  have toll:properThree U-properThree V=FrozenRead.meanOn μ u J-FrozenRead.meanOn μ v J:=by
    rw [signed_proper_weights U V]
    calc
      _=(∑i:Fin 7,w i*U i)-(∑i:Fin 7,w i*V i):=by simp only [mul_sub,Finset.sum_sub_distrib,w]
      _=_:=congrArg₂ (·-·) uj.symm vj.symm
  have eb:Envelope J:=Multi.Leaf.amounts univ (fun i x=>w i*F i x)
    (fun i=>Multi.Leaf.multiply (Multi.Leaf.atom _) (e i))
  refine ⟨toll,?_⟩
  rw [toll]
  exact Replica.reading kn ap bp rm anchor same eb ui vi zp qp

end YM.Integration.FVA1Physical.Exchange.RoseCut
