import YM.Integration.WilsonInvariantActionMixedPrice

/-! The complete complex earlier regular action pair in the genuine retained
Wilson interval, with its original positive lower law and both singleton means. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionRegisteredReturn
open Filter Finset Set MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension OPE OPE.Log Trace.Pilot
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLocalCompactHistory WilsonLocalCompactProbability WilsonInvariantActionMixedMaterial
open WilsonInvariantActionMixedInterval WilsonInheritedRegisteredField Source
open private integr from YM.Integration.WilsonLocalCompactObservation
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I] (R:Run G) {N per b k:ℕ}

theorem source (live:b≤N) (ref:R.family.ref 4≤b) (v:R.family.label 4) (x:Site (R.family.side b per)):
    controlled (regular R.makes live v x) (3*budget v b N per):=by
  let Z:=packet R.makes live v x
  have booked:=WilsonInvariantActionMixedMaterial.filed R.makes live ref v x Set.univ
  have census (U:Config G (R.family.side b per)):
      regular R.makes live v x U=MergeProof.alto R.family.path b 4*Z.x 0+
        primary R.makes live v x U+earlier R.makes live v x Set.univ U:=by
    simp only [regular,Coefficient.exponentialEntry,primary,earlier,Z,Set.mem_univ,if_true,mul_add]
    rfl
  refine ⟨regular_envelope R.makes live ref v x,?_,?_⟩
  · intro g U
    rw [census,census,booked.1.2.1 g U,booked.2.2.1 g U]
  · intro U
    unfold budget
    rw [←mul_assoc]
    exact WilsonRegisteredRegularQuota.original (C:=R.family) R.makes live ref v x U

def returned (cut:b<N) (grade:ℕ) (d:I→ℕ) (T:∀i,i<b→Forest (R.family.path.levels.clock.op i per).ratio)
    (o:∀i,i<b→I→Site (R.family.side (i+1) per)) (live:k≤b) (H:Config G (R.family.side b per)→ℂ):ℂ:=
  ⟨retained R cut grade d T o live (fun U=>(H U).re),retained R cut grade d T o live (fun U=>(H U).im)⟩

def pair {X:Type} (P:(X→ℂ)→ℂ) (F H:X→ℂ):ℂ:=P (fun U=>F U*H U)-P F*P H

private theorem complexFare (A F H:ℂ) (B u v:ℂ) (τ M K:ℝ) (ta:0≤τ) (mp:0≤M) (_kp:0≤K)
    (joint:‖A-B‖≤2*τ*(M*K)) (left:‖F-u‖≤2*τ*M) (right:‖H-v‖≤2*τ*K)
    (size:‖u‖≤M) (other:‖v‖≤K):
    ‖(A-F*H)-(B-u*v)‖≤(6*τ+4*τ^2)*M*K:=by
  have split:(A-F*H)-(B-u*v)=((A-B)-(F-u)*(H-v))-(F-u)*v-u*(H-v):=by ring
  rw [split]
  calc
    _≤‖A-B‖+‖(F-u)*(H-v)‖+‖(F-u)*v‖+‖u*(H-v)‖ :=by
      linarith only [norm_sub_le (A-B) ((F-u)*(H-v)),norm_sub_le ((A-B)-(F-u)*(H-v)) ((F-u)*v),
        norm_sub_le (((A-B)-(F-u)*(H-v))-(F-u)*v) (u*(H-v))]
    _≤2*τ*(M*K)+(2*τ*M)*(2*τ*K)+(2*τ*M)*K+M*(2*τ*K):=by
      simp only [norm_mul];gcongr
    _=(6*τ+4*τ^2)*M*K:=by ring

theorem physical (simple:G.Simple) (pace:WilsonWindowReportingPace.Slow R.kit)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (d:I→ℕ) {B:ℕ} (bp:0<B) (q grade:ℕ) (precision:q+7≤grade) {ε:ℝ} (ep:0<ε):
    ∀ᶠr:ℝ in trail,let b:=WilsonMeasuredWindow.stop R.family.path.levels simple B r
      let j:=WilsonCloseCaptureDate.level R.family.S r
      j≤b ∧ ∀k:ℕ,j≤k→∀live:k≤b,∀N:ℕ,∀cut:b<N,∀per,
      ∀(T:∀i,i<b→Forest (R.family.path.levels.clock.op i per).ratio)
        (o:∀i,i<b→I→Site (R.family.side (i+1) per)) (_birth:R.family.ref 4≤b)
        (x y:Site (R.family.side b per)) (v w:R.family.label 4),
      let F:=regular R.makes cut.le v x
      let H:=regular R.makes cut.le w y
      let μ:=scene R.family.path N per b
      let τ:=ε*regulatorRun R.family N per b^q
      ‖pair (returned R cut grade d T o live) F H-pair (fun f=>∫U,f U ∂μ) F H‖≤
        (6*τ+4*τ^2)*(3*budget v b N per)*(3*budget w b N per):=by
  filter_upwards [WilsonLocalCompactSegmentMean.original R simple pace marks fees d bp q grade precision ep] with r cash
  intro b j
  refine ⟨cash.1,?_⟩
  intro k jk live N cut per T o birth x y v w F H μ τ
  let ν:=scene R.family.path N per k
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson cut.le
  have one (X:Config G (R.family.side b per)→ℝ) (eX:Envelope X) (gX:GaugeInvariant X)
      (M:ℝ) (cap:∀U,|X U|≤M):
      |retained R cut grade d T o live X-physicalMean R N per b X|≤τ*M ∧ |physicalMean R N per b X|≤M:=by
    have transfer:=cash.2 k b jk live le_rfl N cut.le cut per T o X eX gX
    let obs:=program R cut grade d T o X live
    let tr:=actualTransport R.family (N:=N) X live
    have trEnv:=WilsonCoherentEarlier.envelope R.family R.makes cut.le eX live
    have weighted:=actualTransport_weighted_integrable R.family R.makes cut.le (eX.meas.aestronglyMeasurable (μ:=prior G _)) eX.cost.choose_spec le_rfl
    rw [actualTransport_base R.family R.makes cut.le] at weighted
    have preserved:(∫V,tr V ∂ν)=(∫U,X U ∂μ):=actualScene_transport R.family R.makes cut.le weighted live
    have b0:0≤τ:=mul_nonneg ep.le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
    have spend:(∫U,|X U| ∂μ)≤M:=by
      have bounded:Integrable (fun U=>|X U|) μ:=(integr R cut.le eX).abs
      simpa only [integral_const,probReal_univ,one_smul] using
        (integral_mono bounded (integrable_const M) cap)
    constructor
    · change |(∫V,obs V ∂ν)-(∫U,X U ∂μ)|≤τ*M
      rw [←preserved,←integral_sub (integr R (live.trans cut.le) transfer.1) (integr R (live.trans cut.le) trEnv)]
      exact abs_integral_le_integral_abs.trans (transfer.2.2.2.trans (mul_le_mul_of_nonneg_left spend b0))
    · exact abs_integral_le_integral_abs.trans spend

  have single (f:Config G (R.family.side b per)→ℂ) (M:ℝ) (c:controlled f M):
      ‖returned R cut grade d T o live f-(∫U,f U ∂μ)‖≤2*τ*M ∧ ‖∫U,f U ∂μ‖≤M:=by
    have integ:Integrable f μ:=Integrable.of_bound c.1.meas.aestronglyMeasurable M
      (Filter.Eventually.of_forall c.2.2)
    have getRe:=one (fun U=>(f U).re) (signal c Complex.reCLM).2.1 (signal c Complex.reCLM).2.2 M
      (fun U=>(Complex.abs_re_le_norm _).trans (c.2.2 U))
    have getIm:=one (fun U=>(f U).im) (signal c Complex.imCLM).2.1 (signal c Complex.imCLM).2.2 M
      (fun U=>(Complex.abs_im_le_norm _).trans (c.2.2 U))
    constructor
    · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      change |retained R cut grade d T o live _-(∫U,f U ∂μ).re|+
        |retained R cut grade d T o live _-(∫U,f U ∂μ).im|≤_
      have re:(∫U,(f U).re ∂μ)=(∫U,f U ∂μ).re:=integral_re integ
      have im:(∫U,(f U).im ∂μ)=(∫U,f U ∂μ).im:=integral_im integ
      rw [←re,←im]
      exact (add_le_add getRe.1 getIm.1).trans_eq (by ring)
    · refine (norm_integral_le_integral_norm _).trans ?_
      simpa using integral_mono integ.norm (integrable_const M) c.2.2
  let M:=3*budget v b N per;let K:=3*budget w b N per
  have a:=source R cut.le birth v x;have z:=source R cut.le birth w y
  have product:controlled (fun U=>F U*H U) (M*K):=by
    refine ⟨a.1.mulC z.1,fun g U=>congrArg₂ (·*·) (a.2.1 g U) (z.2.1 g U),?_⟩
    intro U
    rw [norm_mul]
    exact mul_le_mul (a.2.2 U) (z.2.2 U) (norm_nonneg _) ((norm_nonneg _).trans (a.2.2 U))
  have left:=single F M a;have right:=single H K z
  exact complexFare _ _ _ _ _ _ τ M K (mul_nonneg ep.le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _))
    ((norm_nonneg _).trans (a.2.2 1)) ((norm_nonneg _).trans (z.2.2 1))
    (single _ _ product).1 left.1 right.1 left.2 right.2

end YM.Integration.WilsonInvariantActionRegisteredReturn
