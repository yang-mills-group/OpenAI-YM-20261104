import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionSevenAction

/-! The reference bank is evaluated only inside its regular aperture. The
seven proper physical moments are first combined with signed coefficients.
The term outside the aperture remains a single genuine signed integral
under the original physical density. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset MeasureTheory Filter RG
open scoped Classical BigOperators
open private linear_mean from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionSevenAction
open private weighted from YM.Integration.FVA1Physical.CommonCover.ReplicaRead
variable {X:Type*}[MeasurableSpace X] {μ:Measure X}

private theorem mass_center {u:X→ℝ}{F:X→ℂ} (ui:Integrable u μ)(up:0<∫x,u x ∂μ)
    (fi:Integrable (fun x=>u x • F x) μ)(q:ℂ):
    (∫x,u x ∂μ) • (FrozenRead.meanOn μ u F-q)=∫x,u x • (F x-q) ∂μ:=by
  dsimp only [FrozenRead.meanOn];simp_rw [smul_sub]
  rw [smul_smul,mul_inv_cancel₀ up.ne',one_smul,integral_sub fi (ui.smul_const q),integral_smul_const]

private theorem aperture_regular_cap [SFinite μ]
    (B:Set X)(bm:MeasurableSet B) {u v r:X→ℝ}
    (ui:Integrable u (μ.restrict B))(vi:Integrable v (μ.restrict B))
    (un:∀x,0≤u x)(vn:∀x,0≤v x)(rm:Measurable r) {t M:ℝ} (tn:0≤t)
    (fee:∀x∈B,∀y∈B,Replica.cap (r x-r y)≤t)
    (F:X→ℂ)(ee:Envelope F)(size:∀x∈B,∀y∈B,‖F x-F y‖≤M):
    let ν:=μ.restrict B
    (∫z,Replica.actionBill u v r z*‖F z.1-F z.2‖ ∂ν.prod ν)≤
      2*(∫x,u x ∂ν)*(∫x,v x ∂ν)*t*M:=by
  intro ν
  have L:Integrable (Replica.cost u v) (ν.prod ν):=ui.mul_prod vi
  have R:Integrable (Replica.cost v u) (ν.prod ν):=vi.mul_prod ui
  have e:=Replica.cost_times_diameter (Replica.integrable_bill ui vi un vn rm) ee
  have allB:∀ᵐ x ∂ν,x∈B:=ae_restrict_mem bm
  have ae1:∀ᵐ z:X×X ∂ν.prod ν,z.1∈B:=Measure.quasiMeasurePreserving_fst.ae allB
  have ae2:∀ᵐ z:X×X ∂ν.prod ν,z.2∈B:=Measure.quasiMeasurePreserving_snd.ae allB
  calc
    _≤∫z,(Replica.cost u v z+Replica.cost v u z)*t*M ∂ν.prod ν:=by
      apply integral_mono_ae e (((L.add R).mul_const t).mul_const M)
      filter_upwards [ae1,ae2] with z hx hy
      let c:=Replica.cost u v z+Replica.cost v u z
      have cn:0≤c:=add_nonneg (mul_nonneg (un _) (vn _)) (mul_nonneg (vn _) (un _))
      change (c*Replica.cap (r z.1-r z.2))*‖F z.1-F z.2‖≤c*t*M
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (fee _ hx _ hy) cn) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (size _ hx _ hy) (mul_nonneg cn tn))
    _=_:=by
      rw [integral_mul_const,integral_mul_const,integral_add L R]
      change ((∫z,u z.1*v z.2 ∂ν.prod ν)+(∫z,v z.1*u z.2 ∂ν.prod ν))*t*M=_
      rw [integral_prod_mul u v,integral_prod_mul v u]
      ring

/-- The regular charge multiplies the oscillation of the whole signed,
proper-face combination. The exceptional expectation retains its phase,
all seven rows, and the true vacuum. No reference moment off B is used. -/
theorem signed_seven_aperture [SFinite μ] (B:Set X)(bm:MeasurableSet B)
    {k a b r:X→ℝ}(km:Measurable k)(am:Measurable a)(bb:Measurable b)(kn:∀x,0≤k x)
    (ap:∀x,0<a x)(bp:∀x,0<b x)(rm:Measurable r)(anchor:ℝ)
    (same:∀x,Real.log (a x)-Real.log (b x)=r x+anchor)
    (t:ℝ)(tn:0≤t)(fee:∀x∈B,∀y∈B,Replica.cap (r x-r y)≤t)
    (F:Fin 7→X→ℂ)(ee:∀i,Envelope (F i)):
    let u:=fun x=>k x*a x;let v:=fun x=>k x*b x;let ν:=μ.restrict B
    let U:=fun i=>FrozenRead.meanOn μ u (F i);let V:=fun i=>FrozenRead.meanOn ν v (F i)
    let J:=fun x=>∑i:Fin 7,properWeights U V i*F i x
    let Q:=FrozenRead.meanOn ν v J
    let z:=∫x,u x ∂μ;let c:=∫x,u x ∂ν;let q:=∫x,v x ∂ν
    Integrable u μ→Integrable v ν→0<z→0<c→0<q→
    (z • (properThree U-properThree V)=c • (FrozenRead.meanOn ν u J-Q)+∫x in Bᶜ,u x • (J x-Q) ∂μ) ∧
    ∀M:ℝ,(∀x∈B,∀y∈B,‖J x-J y‖≤M)→
      z*‖properThree U-properThree V‖≤c*t*M+‖∫x in Bᶜ,u x • (J x-Q) ∂μ‖:=by
  intro u v ν U V J Q z c q ui vi zp cp qp
  let w:=properWeights U V
  have un(x):0≤u x:=mul_nonneg (kn x) (ap x).le
  have vn(x):0≤v x:=mul_nonneg (kn x) (bp x).le
  have uj:=linear_mean μ (km.mul am) ui un zp w F ee
  have vj:=linear_mean ν (km.mul bb) vi vn qp w F ee
  have JE:Envelope J:=Multi.Leaf.amounts univ (fun i x=>w i*F i x)
    (fun i=>Multi.Leaf.multiply (Multi.Leaf.atom _) (ee i))
  have ji:=weighted ui JE
  have d:properThree U-properThree V=FrozenRead.meanOn μ u J-Q:=by
    rw [signed_proper_weights U V]
    calc
      _=(∑i:Fin 7,w i*U i)-(∑i:Fin 7,w i*V i):=by simp only [mul_sub,Finset.sum_sub_distrib,w]
      _=_:=congrArg₂ (·-·) uj.symm vj.symm
  have ein:Integrable (fun x=>u x • (J x-Q)) μ:=by
    simp_rw [smul_sub];exact ji.sub (ui.smul_const Q)
  have split:z • (properThree U-properThree V)=c • (FrozenRead.meanOn ν u J-Q)+∫x in Bᶜ,u x • (J x-Q) ∂μ:=by
    rw [d,mass_center ui zp ji Q,mass_center (μ:=ν) ui.integrableOn cp ji.integrableOn Q]
    exact (integral_add_compl bm ein).symm
  refine ⟨split,?_⟩
  intro M size
  have price:=Replica.reading (μ:=ν) kn ap bp rm anchor same JE ui.integrableOn vi cp qp
  have cap:=aperture_regular_cap B bm ui.integrableOn vi un vn rm tn fee J JE size
  have core:c*‖FrozenRead.meanOn ν u J-Q‖≤c*t*M:=by
    have h:2*q*(c*‖FrozenRead.meanOn ν u J-Q‖)≤2*q*(c*t*M):=by
      calc
        _=2*c*q*‖FrozenRead.meanOn ν u J-Q‖:=by ring
        _≤2*c*q*t*M:=price.trans cap
        _=_:=by ring
    exact le_of_mul_le_mul_left h (by positivity)
  have lhs:=congrArg norm split
  rw [norm_smul,Real.norm_of_nonneg zp.le] at lhs
  rw [lhs]
  refine (norm_add_le ..).trans (add_le_add ?_ le_rfl)
  rw [norm_smul,Real.norm_of_nonneg cp.le]
  exact core

end YM.Integration.FVA1Physical.Exchange.RoseCut
