import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6TrueOneArm

/-! Restore the original Haar field with its exact outer marginal, so
the retained finite thermal moments can be applied to the physical
connected three-field reading. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.F6Regular
open Function Filter Finset MeasureTheory Lattice RG YM.Wilson OPE.Therm Marked.Inherited RoseCut
open scoped Classical BigOperators
open private fillPatch_meas from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6OriginalExterior
open private joined general_measured from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6MeasuredExterior
open private fibre_prob from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionNormalizedConnected
variable {G:Gauge}{n:Side}
local notation "Fld" => Config G n

def outside (I:Finset (Edge (Site n)))(U:Fld)(b:{e:Edge (Site n)//e∉I}):G.El:=U b.1
private theorem external (I:Finset (Edge (Site n))):Measurable (outside (G:=G) I):=by
  apply measurable_pi_lambda;intro b;exact measurable_pi_apply _
private theorem off_filling (I:Finset (Edge (Site n)))(o:{b:Edge (Site n)//b∉I} → G.El)(x:↥I → G.El):
    outside I (fillPatch I o x)=o:=by
  funext b;simp only [outside,fillPatch,dif_neg b.2]

private theorem split_patch (I:Finset (Edge (Site n)))(f:Fld→ℝ)(ef:Envelope f):
    (∫U,f U ∂prior G n)=∫o,∫x,f (fillPatch I o x) ∂Measure.pi (fun _:↥I=>G.probHaar)
      ∂Measure.pi (fun _:{b:Edge (Site n)//b∉I}=>G.probHaar):=by
  let T:=MeasurableEquiv.piEquivPiSubtypeProd (fun _:Edge (Site n)=>G.El) (fun e=>e∈I)
  let η:=Measure.pi (fun _:↥I=>G.probHaar)
  let ζ:=Measure.pi (fun _:{b:Edge (Site n)//b∉I}=>G.probHaar)
  have split:MeasurePreserving T.symm (η.prod ζ) (prior G n):=by
    convert! (measurePreserving_piEquivPiSubtypeProd (fun _:Edge (Site n)=>G.probHaar) (fun e=>e∈I)).symm T
  have eq(x:↥I → G.El)(o:{b:Edge (Site n)//b∉I} → G.El):T.symm (x,o)=fillPatch I o x:=by
    funext b
    by_cases h:b∈I <;> simp [T,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd_symm_apply,fillPatch,h]
  calc (∫U,f U ∂prior G n) = ∫z,f (T.symm z) ∂η.prod ζ:=(split.integral_comp' f).symm
       _=∫o,∫x,f (T.symm (x,o)) ∂η ∂ζ:=integral_prod_symm _ (split.integrable_comp_of_integrable (ef.integrable _))
       _=_:=by simp_rw [eq];rfl

private theorem original_envelope (R:Rep G n){σ C Λ ε ξ:ℝ}(law:R.Lawful σ C Λ ε ξ)(pos:∀u,0<R.eval u)
    (I:Finset (Edge (Site n)))(f:Fld→ℝ)(ef:Envelope f):Envelope (originalOne R I f):=by
  let η:=Measure.pi (fun _:↥I=>G.probHaar)
  have ue:=R.envelope law
  have measurableMass {a:Fld→ℝ}(am:Measurable a):Measurable (fun o=>∫x,a (fillPatch I o x) ∂η):=
    (am.comp (joined I)).stronglyMeasurable.integral_prod_right'.measurable
  refine ⟨(measurableMass (ue.meas.mul ef.meas)).div (measurableMass ue.meas),ef.cost.choose,?_⟩
  intro o
  let J:=fillPatch I o;let u:=R.eval ∘ J;let ν:=fibreLaw η u
  have ew:Envelope u:=⟨ue.meas.comp (fillPatch_meas I o),ue.cost.choose,fun x=>ue.cost.choose_spec _⟩
  have mass:0<∫x,u x ∂η:=by
    apply (integral_pos_iff_support_of_nonneg (fun x=>(pos (J x)).le) (ew.integrable η)).2
    rw [show Function.support (fun x=>R.eval (J x))=Set.univ from Set.eq_univ_of_forall fun x=>(pos (J x)).ne'];simp [η]
  letI:IsProbabilityMeasure ν:=fibre_prob η (ew.integrable η) (fun x=>(pos _).le) mass
  have id:(∫x,f (J x) ∂ν)=originalOne R I f o:=general_measured η ew.meas (fun x=>(pos _).le) _
  rw [←id];simpa only [probReal_univ,mul_one] using (norm_integral_le_of_norm_le_const (μ:=ν) (f:=fun x=>f (J x)) (.of_forall fun x=>ef.cost.choose_spec _))

/-- The three proper-face terms integrate back to the original positive
history. The test on every outside bond retains its joint signs. -/
theorem physical_moment_disintegrates (H:History G)(sel:H.Selected){N j per:ℕ}(live:j≤N)
    (I:Finset (Edge (Site (H.S.side j per))))(f:Config G (H.S.side j per) → ℝ)(ef:Envelope f)
    (Y:({b:Edge (Site (H.S.side j per)) // b∉I} → G.El) → ℝ)(eY:Envelope Y):
    let R:=H.rep N per j;let μ:=originalExterior H N per j I;let τ:=scene H N per j
    (∫o,Y o*originalOne R I f o ∂μ)=∫U,Y (outside I U)*f U ∂τ:=by
  intro R μ τ
  let π:=outside (G:=G) I
  let η:=Measure.pi (fun _:↥I=>G.probHaar)
  have law:=(sel.represents N per j live).good
  have pos:=SectorNext.Vacuum.strictly H sel N per j live
  have ox:Envelope (originalOne R I f):=original_envelope R law pos I f ef
  have pe:=R.envelope law
  have lift {h:({b:Edge (Site (H.S.side j per))//b∉I} → G.El)→ℝ}(eh:Envelope h):Envelope (h ∘ π):=
    ⟨eh.meas.comp (external I),eh.cost.choose,fun x=>eh.cost.choose_spec _⟩
  change (∫o,Y o*originalOne R I f o ∂Measure.map π τ)=_
  rw [integral_map (external I).aemeasurable (eY.mul ox).meas.aestronglyMeasurable,
    scenery sel live,scenery sel live]
  apply congrArg (· / _)
  have A:Envelope (fun U=>R.eval U*(Y (π U)*originalOne R I f (π U))):=pe.mul (lift (eY.mul ox))
  have B:Envelope (fun U=>R.eval U*(Y (π U)*f U)):=pe.mul ((lift eY).mul ef)
  rw [split_patch I _ A,split_patch I _ B]
  apply integral_congr_ae;filter_upwards with o
  change (∫x,R.eval (fillPatch I o x)*(Y (outside I (fillPatch I o x))*originalOne R I f (outside I (fillPatch I o x))) ∂η)=
      ∫x,R.eval (fillPatch I o x)*(Y (outside I (fillPatch I o x))*f (fillPatch I o x)) ∂η
  simp_rw [off_filling]
  rw [integral_mul_const]
  have paid:0<∫x,R.eval (fillPatch I o x) ∂η:=by
    have ew:Envelope (fun x=>R.eval (fillPatch I o x)):=⟨pe.meas.comp (fillPatch_meas I o),pe.cost.choose,fun x=>pe.cost.choose_spec _⟩
    apply (integral_pos_iff_support_of_nonneg (fun x=>(pos _).le) (ew.integrable η)).2
    rw [show Function.support (fun x=>R.eval (fillPatch I o x))=Set.univ from Set.eq_univ_of_forall fun x=>(pos _).ne'];simp [η]
  simp_rw [mul_left_comm (R.eval _) (Y o),integral_const_mul]
  dsimp only [originalOne,rawPatch]
  let z:=∫x,R.eval (fillPatch I o x) ∂η
  let a:=∫x,R.eval (fillPatch I o x)*f (fillPatch I o x) ∂η
  change z*(Y o*(a/z))=Y o*a
  have nz:z≠0:=paid.ne'
  field_simp

end YM.Integration.FVA1Physical.Exchange.F6Regular
