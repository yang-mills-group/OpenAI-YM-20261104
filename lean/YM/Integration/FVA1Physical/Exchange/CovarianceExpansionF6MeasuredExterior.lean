import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6ThreeArms

/-! The actual finite fibre responses are Borel in the original exterior,
including their conditional normalizations. The seven-face difference
can therefore be integrated with its own signed outer fields and terms. -/
set_option autoImplicit false
set_option maxHeartbeats 1550000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.F6Regular
open Function Filter Finset MeasureTheory Lattice RG YM.Wilson OPE.Therm Marked.Inherited RoseCut
open scoped Classical BigOperators
open private fillPatch_meas tilted_probability from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6OriginalExterior
open private subenv from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6RegularCovariance
open private envelope_pair from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6ThreeArms
variable {G:Gauge}{n:Side}
local notation "Fld" => Config G n

private theorem general_measured {Z:Type*}[MeasurableSpace Z](μ:Measure Z){w:Z→ℝ}(wm:Measurable w)(hn:∀x,0≤w x)
    (f:Z→ℝ):(∫x,f x ∂fibreLaw μ w)=(∫x,w x*f x ∂μ)/(∫x,w x ∂μ):=by
  have mn:0≤∫x,w x ∂μ:=integral_nonneg hn
  rw [fibreLaw,integral_withDensity_eq_integral_toReal_smul ((wm.div_const _).ennreal_ofReal) (.of_forall fun _=>ENNReal.ofReal_lt_top),←integral_div]
  apply integral_congr_ae;filter_upwards with x
  rw [ENNReal.toReal_ofReal (div_nonneg (hn _) mn),smul_eq_mul];ring

private theorem joined (I:Finset (Edge (Site n))):Measurable (fun z:({b:Edge (Site n)//b∉I} → G.El) × (↥I → G.El)=>fillPatch I z.1 z.2):=by
  apply measurable_pi_lambda;intro b
  by_cases inside:b∈I
  · simp only [fillPatch,dif_pos inside]
    exact (measurable_pi_apply (⟨b,inside⟩:↥I) : Measurable (fun x:↥I → G.El=>x ⟨b,inside⟩)).comp measurable_snd
  simp only [fillPatch,dif_neg inside]
  exact (measurable_pi_apply (⟨b,inside⟩:{b:Edge (Site n)//b∉I}) :
    Measurable (fun x:({b:Edge (Site n)//b∉I} → G.El)=>x ⟨b,inside⟩)).comp measurable_fst

private theorem normalized_entry (R:Rep G n){σ C Λ ε ξ:ℝ}(law:R.Lawful σ C Λ ε ξ)(pos:∀u,0<R.eval u)
    (I:Finset (Edge (Site n)))(f:Fld→ℝ)(ef:Envelope f):
    Envelope (fun o=>∫x,f (fillPatch I o x) ∂tiltedPatch R I o):=by
  let η:=Measure.pi (fun _:↥I=>G.probHaar)
  let w:=fun u=>R.eval u*Real.exp (R.activities.additive R.p u)
  have ae:Envelope (R.activities.additive R.p):=⟨R.activities.E_measurable law.labels.regular,(Activities.ESeries law.labels).bound⟩
  have we:Envelope w:=(R.envelope law).mul ae.exp
  have nn(u):0≤w u:=mul_nonneg (pos u).le (Real.exp_nonneg _)
  have M{a:Fld→ℝ}(am:Measurable a):Measurable (fun o=>∫x,a (fillPatch I o x) ∂η):=
    (am.comp (joined I)).stronglyMeasurable.integral_prod_right'.measurable
  have eq (o): (∫x,f (fillPatch I o x) ∂tiltedPatch R I o)=
      (∫x,(w (fillPatch I o x)*f (fillPatch I o x)) ∂η)/(∫x,w (fillPatch I o x) ∂η):=
    general_measured η (we.meas.comp (fillPatch_meas I o)) (fun x=>nn _) _
  refine ⟨?_,ef.cost.choose,?_⟩
  · simp_rw [eq];exact (M (we.meas.mul ef.meas)).div (M we.meas)
  intro o
  let ν:=tiltedPatch R I o
  letI:IsProbabilityMeasure ν:=tilted_probability R law pos I o
  change ‖∫x,f (fillPatch I o x) ∂ν‖≤_
  simpa only [probReal_univ,mul_one] using
    (norm_integral_le_of_norm_le_const (μ:=ν) (f:=fun x=>f (fillPatch I o x)) (.of_forall fun x=>ef.cost.choose_spec _))

theorem borel_first_insertion (R:Rep G n){σ C Λ ε ξ:ℝ}(law:R.Lawful σ C Λ ε ξ)(pos:∀u,0<R.eval u)
    (I:Finset (Edge (Site n)))(f D:Fld→ℝ)(ef:Envelope f)(ed:Envelope D):Envelope (patchInsertion R I D f):=by
  let read:=fun (a:Fld→ℝ) o=>∫x,a (fillPatch I o x) ∂tiltedPatch R I o
  have iden:patchInsertion R I D f=(fun o=>read (fun x=>f x*D x) o-read f o*read D o):=by
    funext o
    let J:=fillPatch I o
    let ν:=tiltedPatch R I o
    letI:IsProbabilityMeasure ν:=tilted_probability R law pos I o
    have pull {a:Fld→ℝ}(e:Envelope a):Envelope (a ∘ J):=
      ⟨e.meas.comp (fillPatch_meas I o),e.cost.choose,fun x=>e.cost.choose_spec _⟩
    exact first_is_covariance ν (f ∘ J) (D ∘ J) (pull ef) (pull ed) (D (J 1))
  rw [iden]
  exact subenv (normalized_entry R law pos I _ (ef.mul ed)) ((normalized_entry R law pos I _ ef).mul (normalized_entry R law pos I _ ed))

theorem original_three_covariances {G:Gauge}(H:History G)(sel:H.Selected){N j per:ℕ}(live:j≤N)
    (I:Finset (Edge (Site (H.S.side j per))))(cut:ℕ)(width:1≤(H.rep N per j).p.supportExponent)
    (A:Config G (H.S.side j per)→ℝ)(ea:Envelope A)(M:ℝ)(bound:∀U,|A U|≤M)
    (B C:({b:Edge (Site (H.S.side j per)) // b∉I}→G.El)→ℝ)(eb:Envelope B)(ec:Envelope C):
    let R:=H.rep N per j;let L:=I.image Prod.fst;let μ:=originalExterior H N per j I
    let full:=patchInsertion R I (R.activities.additive R.p) A
    let short:=patchInsertion R I (shortRegular R.activities R.p L cut) A
    |thirdFaces μ full B C-thirdFaces μ short B C|≤
      4*sliceFare R.p (halo 8 L) cut (H.levels.clock.allowance j)*M*(∫o,|centeredPair μ B C o| ∂μ):=by
  intro R L μ full short
  have law:=(sel.represents N per j live).good
  have ep:=SectorNext.Vacuum.strictly H sel N per j live
  letI:IsProbabilityMeasure (scene H N per j):=probability sel live
  have proj:Measurable (fun U:Config G (H.S.side j per)=>fun b:{b:Edge (Site (H.S.side j per)) // b∉I}=>U b.1):=by
    apply measurable_pi_lambda;intro b;exact measurable_pi_apply _
  letI:IsProbabilityMeasure μ:=Measure.isProbabilityMeasure_map proj.aemeasurable
  have all:Envelope (R.activities.additive R.p):=⟨R.activities.E_measurable law.labels.regular,(Activities.ESeries law.labels).bound⟩
  have sl(k):Envelope (sliceLog R.activities R.p (halo 8 L) k):=by
    have p:=hit_slice_log R.activities R.p law.labels.boundE law.labels.regular width (halo 8 L) k;exact ⟨p.1,_,p.2⟩
  have e0:Envelope full:=borel_first_insertion R law ep I A _ ea all
  have e1:Envelope short:=borel_first_insertion R law ep I A _ ea (subenv (sl 0) (sl cut))
  have Y:=envelope_pair μ B C eb ec
  rw [seven_signed_first μ full B C e0 eb ec,seven_signed_first μ short B C e1 eb ec,←integral_sub ((Y.mul e0).integrable μ) ((Y.mul e1).integrable μ)]
  simp_rw [←mul_sub]
  exact paid_three_energies H sel live I cut width A ea M bound B C eb ec

end YM.Integration.FVA1Physical.Exchange.F6Regular
