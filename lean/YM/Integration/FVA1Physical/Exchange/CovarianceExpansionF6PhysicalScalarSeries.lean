import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6OriginalMoments

/-! On one positive physical regulator, the measured three-arm energy
reading is approximated by finite moments of the actual retained regular
tilt. Both remote arms retain their original signed centered product.
The independently constructed order-two coefficients remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.F6Regular
open Function Filter Finset MeasureTheory Lattice RG YM.Wilson OPE.Therm Marked.Inherited RoseCut
open scoped Classical BigOperators
open private joined from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6MeasuredExterior
open private external original_envelope from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6OriginalMoments
open private envelope_pair from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6ThreeArms
variable {G:Gauge}{n:Side}
local notation "Fld" => Config G n

private theorem finite_measurable (R:Rep G n){σ C Λ ε ξ:ℝ}(law:R.Lawful σ C Λ ε ξ)(I:Finset (Edge (Site n)))(f:Fld→ℝ)(fm:Measurable f)(k:ℕ):
    Measurable (finiteOne R I f k):=by
  let η:=Measure.pi (fun _:↥I=>G.probHaar)
  let L:=({b:Edge (Site n)//b∉I} → G.El)
  let J:=fun z:L×(↥I → G.El)=>fillPatch I z.1 z.2
  let V:=fun z:L×(↥I → G.El)=>fillPatch I z.1 1
  let D:=fun z=>R.activities.additive R.p (J z)-R.activities.additive R.p (V z)
  let w:=fun z=>R.eval (J z)*(Real.exp (D z)*tiltTaylor k (-D z))
  have j:Measurable J:=joined I
  have v:Measurable V:= j.comp (measurable_fst.prodMk (measurable_const (a:=(1:↥I→G.El))))
  have d:Measurable D:=((R.activities.E_measurable law.labels.regular).comp j).sub ((R.activities.E_measurable law.labels.regular).comp v)
  have poly:Continuous (tiltTaylor k):=by unfold tiltTaylor;fun_prop
  have wm:Measurable w:=((R.envelope law).meas.comp j).mul ((Real.continuous_exp.measurable.comp d).mul (poly.measurable.comp d.neg))
  exact ((wm.mul (fm.comp j)).stronglyMeasurable.integral_prod_right' (ν:=η)).measurable.div
    (wm.stronglyMeasurable.integral_prod_right' (ν:=η)).measurable

/-- The original connected physical reading, formed from all seven common
moments, versus the finite polynomial on the near-energy conditional. The
true centered exterior remains inside the original marginal. -/
theorem physical_three_energy_series (H:History G)(sel:H.Selected){N j per:ℕ}(live:j≤N)
    (I:Finset (Edge (Site (H.S.side j per))))(width:1≤(H.rep N per j).p.supportExponent)
    (A:Config G (H.S.side j per)→ℝ)(ea:Envelope A)(M:ℝ)(bound:∀U,|A U|≤M)(k:ℕ)
    (B C:({b:Edge (Site (H.S.side j per)) // b∉I}→G.El)→ℝ)(eb:Envelope B)(ec:Envelope C):
    let R:=H.rep N per j;let L:=I.image Prod.fst;let μ:=originalExterior H N per j I;let τ:=scene H N per j
    let π:=outside (G:=G) I
    let ω:=((halo 8 L).card:ℝ)*(2*Push.GridApprox.Attach.hitConstant R.p.B*H.levels.clock.allowance j)
    ω≤1/4 → |thirdFaces τ A (B ∘ π) (C ∘ π)-(∫o,centeredPair μ B C o*finiteOne R I A k o ∂μ)|≤
      8*M*ω^(k+1)*(∫o,|centeredPair μ B C o| ∂μ):=by
  intro R L μ τ π ω small
  have law:=(sel.represents N per j live).good
  have pos:=SectorNext.Vacuum.strictly H sel N per j live
  letI:IsProbabilityMeasure τ:=probability sel live
  letI:IsProbabilityMeasure μ:=Measure.isProbabilityMeasure_map (external I).aemeasurable
  have pull {f:({b:Edge (Site (H.S.side j per))//b∉I} → G.El)→ℝ}(ef:Envelope f):Envelope (f ∘ π):=
    ⟨ef.meas.comp (external I),ef.cost.choose,fun x=>ef.cost.choose_spec _⟩
  have mapMean {f:({b:Edge (Site (H.S.side j per))//b∉I} → G.El)→ℝ}(ef:Envelope f):
      (∫o,f o ∂μ)=∫U,f (π U) ∂τ:=integral_map (external I).aemeasurable ef.meas.aestronglyMeasurable
  have c_id(U):centeredPair μ B C (π U)=centeredPair τ (B ∘ π) (C ∘ π) U:=by
    unfold centeredPair
    rw [mapMean eb,mapMean ec,mapMean (eb.mul ec)]
    rfl
  have yr:=envelope_pair μ B C eb ec
  have three:thirdFaces τ A (B ∘ π) (C ∘ π)=(∫o,centeredPair μ B C o*originalOne R I A o ∂μ):=by
    rw [seven_signed_first τ A _ _ ea (pull eb) (pull ec),physical_moment_disintegrates H sel live I A ea (centeredPair μ B C) yr]
    apply integral_congr_ae;filter_upwards with U;rw [←c_id]
  have orig:=original_envelope R law pos I A ea
  have apo:Envelope (finiteOne R I A k):=by
    refine ⟨finite_measurable R law I A ea.meas k,8*M*ω^(k+1)+orig.cost.choose,?_⟩
    intro o
    have step:=norm_le_insert' (finiteOne R I A k o) (originalOne R I A o)
    have e:=original_one_finite R law pos I width A ea M bound k o small
    have q:=orig.cost.choose_spec o
    simpa only [Real.norm_eq_abs] using (step.trans ((add_le_add q e).trans_eq (add_comm ..)))
  rw [three,abs_sub_comm,←integral_sub ((yr.mul apo).integrable μ) ((yr.mul orig).integrable μ)]
  simp_rw [←mul_sub]
  exact original_exterior_thermal H sel live I width A ea M bound k B C eb ec small

end YM.Integration.FVA1Physical.Exchange.F6Regular
