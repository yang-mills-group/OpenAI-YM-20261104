import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6OriginalExterior

/-! The signed three-field regular insertion, with the centering of the
two exterior arms on their original joint law. The first field need not
be independent of either exterior energy. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.F6Regular
open Function Filter Finset MeasureTheory Lattice RG YM.Wilson OPE.Therm Marked.Inherited
open scoped Classical BigOperators
open private subenv from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6RegularCovariance
variable {Z:Type*}[MeasurableSpace Z]

def centeredPair (μ:Measure Z)(B C:Z→ℝ)(z:Z):ℝ:=
  let b:=∫u,B u ∂μ;let c:=∫u,C u ∂μ
  (B z-b)*(C z-c)-((∫u,B u*C u ∂μ)-b*c)

def thirdFaces (μ:Measure Z)(A B C:Z→ℝ):ℝ:=
  (∫u,A u*B u*C u ∂μ)-(∫u,A u*B u ∂μ)*(∫u,C u ∂μ)-
  (∫u,A u*C u ∂μ)*(∫u,B u ∂μ)-(∫u,B u*C u ∂μ)*(∫u,A u ∂μ)+
  2*(∫u,A u ∂μ)*(∫u,B u ∂μ)*(∫u,C u ∂μ)

theorem first_is_covariance (μ:Measure Z)[IsProbabilityMeasure μ](f D:Z→ℝ)(fe:Envelope f)(de:Envelope D)(c:ℝ):
    firstRead μ f (fun z=>D z-c)=(∫z,f z*D z ∂μ)-(∫z,f z ∂μ)*(∫z,D z ∂μ):=by
  let m:=∫z,f z ∂μ
  let h:=fun z=>f z-m
  have he:Envelope h:=subenv fe (Envelope.const m)
  have null:(∫z,h z ∂μ)=0:=by
    dsimp only [h]
    rw [integral_sub (fe.integrable μ) (integrable_const _)]
    simp [m]
  unfold firstRead
  change (∫z,h z*(D z-c) ∂μ)=_
  simp_rw [mul_sub]
  rw [integral_sub ((he.mul de).integrable μ) ((he.integrable μ).mul_const c),integral_mul_const,null,zero_mul,sub_zero]
  simp only [h,sub_mul];rw [integral_sub ((fe.mul de).integrable μ) ((de.integrable μ).const_mul m),integral_const_mul]

private theorem envelope_pair (μ:Measure Z)(B C:Z→ℝ)(eb:Envelope B)(ec:Envelope C):Envelope (centeredPair μ B C):=
  subenv ((subenv eb (Envelope.const _)).mul (subenv ec (Envelope.const _))) (Envelope.const _)

/-- A whole signed response of the near arm enters all seven nonempty faces
with their true common vacuum. This is the exact tested functional. -/
theorem seven_signed_first (μ:Measure Z)[IsFiniteMeasure μ](A B C:Z→ℝ)(ea:Envelope A)(eb:Envelope B)(ec:Envelope C):
    thirdFaces μ A B C=∫z,centeredPair μ B C z*A z ∂μ:=by
  let b:=∫z,B z ∂μ;let c:=∫z,C z ∂μ;let bc:=∫z,B z*C z ∂μ
  have eq(z):centeredPair μ B C z*A z=
    A z*B z*C z-A z*B z*c-A z*C z*b-A z*bc+A z*(2*b*c):=by
    dsimp only [centeredPair,b,c,bc];ring
  have abc:=((ea.mul eb).mul ec).integrable μ
  have ab:=((ea.mul eb).integrable μ).mul_const c
  have ac:=((ea.mul ec).integrable μ).mul_const b
  have aBC:=(ea.integrable μ).mul_const bc
  have aK:=(ea.integrable μ).mul_const (2*b*c)
  have t1:Integrable (fun z=>A z*B z*C z-A z*B z*c) μ:=abc.sub ab
  have t2:Integrable (fun z=>A z*B z*C z-A z*B z*c-A z*C z*b) μ:=t1.sub ac
  have t3:Integrable (fun z=>A z*B z*C z-A z*B z*c-A z*C z*b-A z*bc) μ:=t2.sub aBC
  simp_rw [eq]
  rw [integral_add t3 aK,integral_sub t2 aBC,integral_sub t1 ac,integral_sub abc ab]
  simp only [integral_mul_const,thirdFaces,b,c,bc];ring

theorem paid_three_energies {G:Gauge}(H:History G)(sel:H.Selected){N j per:ℕ}(live:j≤N)
    (I:Finset (Edge (Site (H.S.side j per))))(cut:ℕ)(width:1≤(H.rep N per j).p.supportExponent)
    (A:Config G (H.S.side j per)→ℝ)(eA:Envelope A)(M:ℝ)(bound:∀U,|A U|≤M)
    (B C:({b:Edge (Site (H.S.side j per)) // b∉I}→G.El)→ℝ)(eB:Envelope B)(eC:Envelope C):
    let R:=H.rep N per j;let L:=I.image Prod.fst;let μ:=originalExterior H N per j I
    let D:=fun o=>patchInsertion R I (R.activities.additive R.p) A o-
      patchInsertion R I (shortRegular R.activities R.p L cut) A o
    |∫o,centeredPair μ B C o*D o ∂μ|≤
      4*sliceFare R.p (halo 8 L) cut (H.levels.clock.allowance j)*M*(∫o,|centeredPair μ B C o| ∂μ):=by
  intro R L μ D
  let nonzero:IsProbabilityMeasure (scene H N per j):=probability sel live
  letI:=nonzero
  have projection:Measurable (fun U:Config G (H.S.side j per)=>fun b:{b:Edge (Site (H.S.side j per)) // b∉I}=>U b.1):=by
    apply measurable_pi_lambda;intro b;exact measurable_pi_apply _
  letI:IsProbabilityMeasure μ:=Measure.isProbabilityMeasure_map projection.aemeasurable
  exact actual_exterior_first_insertion H sel live I cut width A eA M bound (centeredPair μ B C) ((envelope_pair μ B C eB eC).integrable μ)

end YM.Integration.FVA1Physical.Exchange.F6Regular
