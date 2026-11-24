import YM.Integration.WilsonMatrixTicketLanesRegisteredHearing
import YM.Integration.WilsonMatrixTicketLanesRegisteredCovariance

/-! At zero prior perturbation the jointly differentiated test is the original
complex signed measured covariance on the earlier regulator, after both original centers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRegisteredValue
open Filter Function Finset MeasureTheory Lattice RG Wilson FullVolume Table
open OPE.Therm PhysicalNext.Repeat.Legato WilsonInheritedRegisteredField WilsonInvariantActionPriorHearing
open WilsonMatrixTicketLanesRegisteredHearing WilsonInvariantActionRegisteredHearing
open WilsonInvariantActionConditionalMarginal WilsonInvariantActionRegisteredReturn
open private conserved from YM.Integration.WilsonInvariantActionConditionalMarginal
open private integral from YM.Integration.WilsonInvariantActionConditionalRegistered
open private product from YM.Integration.WilsonMatrixTicketLanesRegisteredCovariance
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {k N per:ℕ}
local notation "upper" => Config G (R.family.side (k+1) per)
local notation "lower" => Config G (R.family.side k per)
local notation "Ω" => (lower×upper)
local notation "μ" => scene R.family.path N per (k+1)
local notation "κ" => ActualWilsonConditionalRoots.fibre R.family (N:=N)
local notation "Sites" => (Fin 2 → Site (R.family.side N per))

private theorem reint {X:Type*} [MeasurableSpace X] {ν:Measure X} {f:X → ℂ} (hf:Integrable f ν):
    (∫U,f U ∂ν).re=∫U,(f U).re ∂ν:=(_root_.integral_re hf).symm
private theorem imint {X:Type*} [MeasurableSpace X] {ν:Measure X} {f:X → ℂ} (hf:Integrable f ν):
    (∫U,f U ∂ν).im=∫U,(f U).im ∂ν:=(_root_.integral_im hf).symm

private theorem fine (live:k<N) (a:readings Ω) (same:∀(V:lower)(U:upper),a.val (V,U)=a.val (1,U)):
    joint R (p:=per) live a=∫U,a.val (1,U) ∂μ:=by
  let b:=fun U:upper=>a.val (1,U)
  have eb:Envelope b:=⟨a.property.meas.comp (measurable_const.prodMk measurable_id),_,fun U=>a.property.cost.choose_spec (1,U)⟩
  let c:=fun U=>(b U:ℂ)
  have ec:Envelope c:=⟨Complex.continuous_ofReal.measurable.comp eb.meas,eb.cost.choose,fun U=>by
    simpa only [c,Complex.norm_real] using eb.cost.choose_spec U⟩
  have conservedValue:=conserved R live c ec
  have marginal:=congrArg Complex.re conservedValue.2
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson live
  rw [reint conservedValue.1,reint (integral ec)] at marginal
  have fibre (V:lower): (mean R (N:=N) c V).re=∫U,a.val (V,U) ∂κ V:=by
    letI:=ActualWilsonConditionalRoots.probability R.family R.makes live V
    unfold mean;rw [reint (integral ec)]
    simp only [c,Complex.ofReal_re,b,same V]
  change (∫ V:lower, (∫ U:upper, a.val (V,U) ∂κ V) ∂scene R.family.path N per k)=_
  simpa only [fibre,c,b,Complex.ofReal_re] using marginal

private theorem tested {α:Type*} [MeasurableSpace α] (ν:Measure α) [IsFiniteMeasure ν]
    (f h:α → ℂ) (ef:Envelope f) (eh:Envelope h) (χ:ℂ →L[ℝ]ℝ) (w:ℂ):
    channel χ w (fun η θ=>(∫U,η (f U)*θ (h U) ∂ν)-(∫U,η (f U) ∂ν)*(∫U,θ (h U) ∂ν))=
    χ (w*((∫U,f U*h U ∂ν)-(∫U,f U ∂ν)*(∫U,h U ∂ν))):=by
  have coords(z:ℂ):χ (w*z)=χ w*z.re+χ (w*Complex.I)*z.im:=by
    have mul:w*z=z.re • w+z.im • (w*Complex.I):=by
      rw [Complex.real_smul,Complex.real_smul]
      nth_rw 1 [←Complex.re_add_im z]
      ring
    rw [mul,map_add,map_smul,map_smul]
    change z.re*χ w+z.im*χ (w*Complex.I)=_
    ring
  have proj (h:α → ℂ) (paid:Envelope h) (η:ℂ →L[ℝ]ℝ):Envelope (fun U=>η (h U)):=by
    exact ⟨η.continuous.measurable.comp paid.meas,‖η‖*paid.cost.choose,fun U=>(η.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (paid.cost.choose_spec U) (norm_nonneg _))⟩
  have both (η θ:ℂ →L[ℝ]ℝ):Integrable (fun U=>η (f U)*θ (h U)) ν:=
    ((proj f ef η).mul (proj h eh θ)).integrable ν
  have zh:Integrable (fun U=>f U*h U) ν:=integral (product ef eh)
  have re: (∫U,f U*h U ∂ν).re=(∫U,(f U).re*(h U).re ∂ν)-(∫U,(f U).im*(h U).im ∂ν):=by
    rw [reint zh];simp only [Complex.mul_re]
    exact integral_sub (both Complex.reCLM Complex.reCLM) (both Complex.imCLM Complex.imCLM)
  have im: (∫U,f U*h U ∂ν).im=(∫U,(f U).re*(h U).im ∂ν)+(∫U,(f U).im*(h U).re ∂ν):=by
    rw [imint zh];simp only [Complex.mul_im]
    exact integral_add (both Complex.reCLM Complex.imCLM) (both Complex.imCLM Complex.reCLM)
  rw [coords,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,re,im,
    reint (integral ef),imint (integral ef),
    reint (integral eh),imint (integral eh)]
  simp only [channel,Complex.reCLM_apply,Complex.imCLM_apply]
  ring

theorem original (inside:k+1<N) (birth:R.family.ref 4 ≤ k+1) (v:Fin 2 → R.family.label 4)
    (φ:Test 2) (χ:ℂ →L[ℝ]ℝ) (numerator:Sites → readings Ω):
    variation R inside birth v φ χ numerator 0=χ (WilsonInvariantActionCapturedProfile.earlier R (per:=per) inside.le v φ):=by
  let live:k<N:=Nat.lt_trans (Nat.lt_succ_self k) inside
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson inside.le
  unfold variation panel WilsonInvariantActionCapturedProfile.earlier
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  let o:=fun i=>(R.family.S.toDepth inside.le per).parent (x i)
  let f:=regular (C:=R.family) R.makes inside.le (v 0) (o 0)
  let h:=regular (C:=R.family) R.makes inside.le (v 1) (o 1)
  have eqn(η θ:ℂ →L[ℝ]ℝ):covariance
      (reweighted (joint R (p:=per) live) (score R inside (numerator x)) 0)
      (filed R live birth (v 0) (o 0) η) (filed R live birth (v 1) (o 1) θ)=
      (∫U,η (f U)*θ (h U) ∂μ)-(∫U,η (f U) ∂μ)*(∫U,θ (h U) ∂μ):=by
    simp only [covariance,reweighted,zero_mul,add_zero,div_one]
    rw [fine R live _ (fun _ _=>rfl),fine R live _ (fun _ _=>rfl),fine R live _ (fun _ _=>rfl)]
    rfl
  change channel χ _ (fun η θ=>covariance _ (filed R live birth (v 0) (o 0) η) (filed R live birth (v 1) (o 1) θ))=_
  simp_rw [eqn]
  exact tested _ f h (regular_envelope (C:=R.family) R.makes inside.le birth _ _)
    (regular_envelope (C:=R.family) R.makes inside.le birth _ _) χ _

end YM.Integration.WilsonMatrixTicketLanesRegisteredValue
