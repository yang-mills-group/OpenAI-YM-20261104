import YM.Integration.WilsonInvariantActionMixedMaterial
import YM.Integration.WilsonLocalCompactSegmentMean

/-! The signed mixed primary/earlier measured coefficient, including its two
proper means, through the genuine nonbare compact reporting program on the
whole close interval and the unchanged earlier Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionMixedInterval
open Filter Finset Set MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension OPE OPE.Log Trace.Pilot
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLocalCompactHistory WilsonLocalCompactProbability WilsonInvariantActionMixedMaterial
open private integr from YM.Integration.WilsonLocalCompactObservation
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I] (R:Run G) {N per l k:ℕ}

def retained (cut:l<N) (grade:ℕ) (d:I→ℕ) (T:∀i,i<l→Forest (R.family.path.levels.clock.op i per).ratio)
    (o:∀i,i<l→I→Site (R.family.side (i+1) per)) (live:k≤l) (H:Config G (R.family.side l per)→ℝ):ℝ:=
  ∫V,program R cut grade d T o H live V ∂scene R.family.path N per k

def physicalMean (N per k:ℕ) (H:Config G (R.family.side k per)→ℝ):ℝ:=
  ∫U,H U ∂scene R.family.path N per k

def pair {X:Type} (P:(X→ℝ)→ℝ) (F H:X→ℝ):ℝ:=P (fun U=>F U*H U)-P F*P H

private theorem scalar (A B a b u v τ M K:ℝ) (ta:0≤τ) (Mp:0≤M)
    (product:|A-B|≤τ*(M*K)) (left:|a-u|≤τ*M) (right:|b-v|≤τ*K)
    (small:|u|≤M) (low:|v|≤K):
    |(A-a*b)-(B-u*v)|≤(3*τ+τ^2)*M*K:=by
  have val:(A-a*b)-(B-u*v)=((A-B)-(a-u)*(b-v))-(a-u)*v-u*(b-v):=by ring
  rw [val]
  have triangle (x y:ℝ):|x-y|≤|x|+|y|:=by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le x (-y)
  calc
    _ ≤ ((|A-B|+|(a-u)*(b-v)|)+|(a-u)*v|)+|u*(b-v)|:=
      (triangle (((A-B)-(a-u)*(b-v))-(a-u)*v) (u*(b-v))).trans (add_le_add
        ((triangle ((A-B)-(a-u)*(b-v)) ((a-u)*v)).trans
          (add_le_add (triangle (A-B) ((a-u)*(b-v))) le_rfl)) le_rfl)
    _ ≤ ((τ*(M*K)+(τ*M)*(τ*K))+(τ*M)*K)+M*(τ*K):=by
      simp only [abs_mul]
      exact add_le_add (add_le_add (add_le_add product (mul_le_mul left right (abs_nonneg _) (mul_nonneg ta Mp)))
        (mul_le_mul left low (abs_nonneg _) (mul_nonneg ta Mp))) (mul_le_mul small right (abs_nonneg _) Mp)
    _ = _:=by ring

theorem integrated (simple:G.Simple) (pace:WilsonWindowReportingPace.Slow R.kit)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (d:I→ℕ) {B:ℕ} (bp:0<B) (q grade:ℕ) (precision:q+7≤grade) {ε:ℝ} (ep:0<ε):
    ∀ᶠr:ℝ in trail,let b:=WilsonMeasuredWindow.stop R.family.path.levels simple B r
      let j:=WilsonCloseCaptureDate.level R.family.S r
      j≤b ∧ ∀k:ℕ,j≤k→∀live:k≤b,∀N:ℕ,∀cut:b<N,∀per,
      ∀(T:∀i,i<b→Forest (R.family.path.levels.clock.op i per).ratio)
        (o:∀i,i<b→I→Site (R.family.side (i+1) per)) (_birth:R.family.ref 4≤b)
        (x y:Site (R.family.side b per)) (v w:R.family.label 4) (cohort:Set ℕ) (η χ:ℂ→L[ℝ]ℝ),
      let F:=fun U=>η (primary R.makes cut.le v x U)
      let H:=fun U=>χ (earlier R.makes cut.le w y cohort U)
      let τ:=ε*regulatorRun R.family N per b^q
      |pair (retained R cut grade d T o live) F H-pair (physicalMean R N per b) F H|≤
        (3*τ+τ^2)*(‖η‖*budget v b N per)*(‖χ‖*budget w b N per):=by
  filter_upwards [WilsonLocalCompactSegmentMean.original R simple pace marks fees d bp q grade precision ep] with r cash
  intro b j
  refine ⟨cash.1,?_⟩
  intro k jk live N cut per T o birth x y v w cohort η χ F H τ
  let μ:=scene R.family.path N per b
  let ν:=scene R.family.path N per k
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson cut.le
  have fp:=(WilsonInvariantActionMixedMaterial.filed R.makes cut.le birth v x cohort).1
  have hp:=(WilsonInvariantActionMixedMaterial.filed R.makes cut.le birth w y cohort).2
  let c:=‖η‖*budget v b N per;let t:=‖χ‖*budget w b N per
  have fc (U):|F U|≤c:=value fp η U
  have hc (U):|H U|≤t:=value hp χ U
  have goodF:Envelope F ∧ GaugeInvariant F:=(signal fp η).2
  have goodH:Envelope H ∧ GaugeInvariant H:=(signal hp χ).2
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
  have product:=one (fun U=>F U*H U) (goodF.1.mul goodH.1) (fun g U=>congrArg₂ (·*·) (goodF.2 g U) (goodH.2 g U))
    (c*t) (fun U=>by rw [abs_mul];exact mul_le_mul (fc U) (hc U) (abs_nonneg _) ((abs_nonneg _).trans (fc U)))
  have a:=one F goodF.1 goodF.2 c fc
  have b:=one H goodH.1 goodH.2 t hc
  exact scalar _ _ _ _ _ _ τ c t (mul_nonneg ep.le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _))
    ((abs_nonneg _).trans a.2) product.1 a.1 b.1 a.2 b.2

end YM.Integration.WilsonInvariantActionMixedInterval
