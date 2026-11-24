import YM.Integration.WilsonMeasuredInheritedGauge
import YM.Integration.WilsonCoherentRetainedExperiment

/-! A positive two-date covariance with a true degree-four birth at each
end. On the occupied reporting collar, the single fresh field has its
actual factory coordinate and engineering factor in the finite chart
polynomial. The signed unobserved complement retains both fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredDegreeFourCovariance
open Function Filter Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension Push.SectorMeasure
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm
open RG16 ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction Pert.Asymptotics
open WilsonReportingForestPivots WilsonCoherentForestMeasure WilsonCoherentForestReadout
open WilsonIncidentRegisteredMass WilsonCoherentMeasuredStencil WilsonCoherentMeasuredChart
open private indicator_env from YM.Integration.WilsonAcceptedLinkWeight
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "D" => R.family.path

private theorem real_test {X:Type*} [MeasurableSpace X] {f:X→ℂ} (e:Envelope f)
    (η:ℂ→L[ℝ]ℝ) : Envelope (fun x=>η (f x)) := by
  obtain ⟨M,h⟩:=e.cost
  exact ⟨η.continuous.measurable.comp e.meas,‖η‖*M,fun x=>
    (η.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h x) (norm_nonneg _))⟩

private theorem centered (N per j:ℕ) (live:j+1≤N) (V:Config G (R.family.side j per))
    (C:Set (Config G (R.family.side (j+1) per))) (event:MeasurableSet C)
    (F b:Config G (R.family.side (j+1) per)→ℝ) (eF:Envelope F) (eb:Envelope b) :
    let E:=actualAverage R.family (N:=N) (p:=per) (m:=j) (E:=ℝ)
    let H:=fun U=>F U-E F V
    E (fun U=>F U*b U) V-E F V*E b V-E (Cᶜ.indicator (fun U=>H U*b U)) V =
      E (C.indicator (fun U=>H U*b U)) V := by
  intro E H
  let Q:=(D).rep N per (j+1)
  let a:=actualConditionalDensity R.family N per j V
  let μ:=prior G (R.family.side (j+1) per)
  obtain ⟨c,hc,low⟩:=WilsonHeldExteriorLaw.upper_floor R N per j live
  have ea:Envelope a:=(WilsonHeldExteriorLaw.regularity R N per j live V Q
    (Q.envelope (R.makes.wilson.represents N per (j+1) live).good) hc low).1
  have eh:Envelope H:=by
    simpa only [H,sub_eq_add_neg] using eF.add (Envelope.const (-E F V))
  let G':=fun U=>H U*b U
  have whole:Envelope G':=eh.mul eb
  have balance:E (fun U=>F U*b U) V-E F V*E b V=∫U,a U*G' U ∂μ:=by
    change (∫U,a U*(F U*b U) ∂μ)-E F V*(∫U,a U*b U ∂μ)=_
    rw [←integral_const_mul,←integral_sub ((ea.mul (eF.mul eb)).integrable μ)
      (((ea.mul eb).integrable μ).const_mul (E F V))]
    apply integral_congr_ae;apply ae_of_all;intro U
    change a U*(F U*b U)-E F V*(a U*b U)=a U*((F U-E F V)*b U);ring
  have split:∫U,a U*G' U ∂μ=E (C.indicator G') V+E (Cᶜ.indicator G') V:=by
    change _=(∫U,a U*C.indicator G' U ∂μ)+∫U,a U*Cᶜ.indicator G' U ∂μ
    rw [←integral_add ((ea.mul (indicator_env event whole)).integrable μ)
      ((ea.mul (indicator_env event.compl whole)).integrable μ)]
    apply integral_congr_ae;apply ae_of_all;intro U
    by_cases h:U∈C <;> simp [h]
  rw [balance,split];ring

/-- Before all cutoffs and periods, the part of the original full covariance
carried by the reported event is read in the corrected retained forest law
against the genuine previously evolved observable, still at the same gauge. -/
theorem purchased (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (D).levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) (hp:LocalRatio P) {r:ℝ} (pr:0<r) (sr:r<Chart.small G P)
    (q grade:ℕ) (order:q+5≤grade) {ε:ℝ} (he:0<ε) :
    let d:Unit→ℕ:=fun _=>4
    ∀ᶠ m:ℕ in atTop,∀ N (interior:m+1<N) per (v w:R.family.label 4)
      (x:Site (R.family.side N per)) (o:Site (R.family.side (m+1) per))
      (T:Forest ((D).levels.clock.op m per).ratio) (V:Config G (R.family.side m per))
      (η χ:ℂ→L[ℝ]ℝ),
    let roots:Unit→Site (R.family.side (m+1) per):=fun _=>o
    let y:∀i,R.family.label (d i):=fun _=>(R.family.factory 4 (m+1) per).terminal.symm w
    let α:=(((R.family.S.a (m+1):ℂ)^4)⁻¹)
    let F:=fun U=>η (actualTransport R.family (N:=N) (R.family.O N per v x) interior.le U)
    let b:=fun U=>χ (R.family.O (m+1) per w o U)
    let E:=actualAverage R.family (N:=N) (p:=per) (m:=m) (E:=ℝ)
    let old:=fun U=>F U-E F V
    let B:=incident R T d roots
    let C:=cold R m per d roots
    let θ:=((D).rep N per (m+1)).p.threshold
    let δ:=ε*regulatorRun R.family N per (m+1)^q
    let retained:=∫z in panel R m per d roots T r,
      WilsonCoherentRetainedDriver.value R interior grade T B V z*old (state T B z)*
        χ (α*polynomial T B R d θ y roots (q+2*reserve R d) z) ∂law P r T B
    |E (fun U=>F U*b U) V-E F V*E b V-E (Cᶜ.indicator (fun U=>old U*b U)) V-retained|≤
      δ*E (C.indicator (fun U=>|old U*b U|)) V+
      (2*((‖χ‖*‖α‖)*(δ*originalMass R d y)))*E (C.indicator (fun U=>|old U|)) V := by
  intro d
  filter_upwards [WilsonCoherentRetainedExperiment.measured R simple marks fees slow J clear P hp pr sr d q grade order he,
    WilsonCoherentMeasuredStencil.on_event R d simple] with m paid present N interior per v w x o T V η χ
  intro roots y α F b E old B C θ δ retained
  let A:=actualTransport R.family (N:=N) (R.family.O N per v x) interior.le
  have inherited:=WilsonMeasuredInheritedGauge.occupied R.family R.makes (per:=per) interior.le v x
  have eF:Envelope F:=real_test inherited.1 η
  have eB:Envelope b:=real_test (Env.compact (R.family.continuousO (m+1) per 4 w o)) χ
  have eOld:Envelope old:=by simpa only [old,sub_eq_add_neg] using eF.add (Envelope.const (-E F V))
  have gOld:GaugeInvariant old:=fun t U=>congrArg (fun a=>η a-E F V) (inherited.2 t U)
  have tested:=paid N interior per y roots T V α χ old eOld gOld
  let f:=fun U=>χ (α*∏i,Push.Local.primary (R.family.localSection (d i)) (roots i) θ (y i) U)
  have same (U) (clean:U∈C):b U=f U:=by
    have original:=present N per interior.le roots y U clean
    have threshold:((D).rep N per (m+1)).p.threshold=(D).levels.clock.threshold (m+1):=
      congrArg (fun a=>a.threshold) (R.makes.wilson.represents N per (m+1) interior.le).vac
    rw [show f U=χ (α*∏i,Push.Local.primary (R.family.localSection (d i)) (roots i) θ (y i) U) from rfl,←original,threshold]
    simp only [Fintype.prod_unique]
    rfl
  have change (φ:ℝ→ℝ):C.indicator (fun U=>φ (old U*f U))=C.indicator (fun U=>φ (old U*b U)):=by
    funext U;by_cases clean:U∈C
    · simp only [indicator_of_mem clean,same U clean]
    · simp only [indicator_of_notMem clean]
  have eC:MeasurableSet C:=MeasurableSet.iInter (fun _=>House.bath _)
  have split:=centered R N per m interior.le V C eC F b eF eB
  rw [split]
  change |E (C.indicator (fun U=>old U*f U)) V-retained|≤
    δ*E (C.indicator (fun U=>|old U*f U|)) V+
      (2*((‖χ‖*‖α‖)*(δ*originalMass R d y)))*E (C.indicator (fun U=>|old U|)) V at tested
  have first:=change id
  simp only [id_eq] at first
  rw [first,change abs] at tested
  exact tested

end YM.Integration.WilsonRegisteredDegreeFourCovariance
end
