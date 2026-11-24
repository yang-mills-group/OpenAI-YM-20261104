import YM.Integration.WilsonCoherentRegisteredExperiment
import YM.Integration.WilsonCoherentRetainedDriver
import YM.Integration.WilsonCoherentRetainedIntegral

/-! The original normalized registered observable against its retained Wilson
driver and its declared finite marked polynomial. The positive exterior
marginal and the whole correlated spectator stay inside the same integral. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentRetainedExperiment
open Function Filter Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm
open RG16 ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction Pert.Asymptotics
open WilsonReportingForestPivots WilsonCoherentForestMeasure WilsonCoherentForestReadout
open WilsonIncidentRegisteredMass WilsonCoherentMeasuredStencil WilsonCoherentMeasuredChart
open scoped Classical Topology
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]
local notation "A" => R.family.path

theorem measured (simple:G.Simple) (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A).levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) (hp:LocalRatio P) {r:ℝ} (pr:0<r) (sr:r<Chart.small G P)
    (d:I→ℕ) (q grade:ℕ) (order:q+5≤grade) {ε:ℝ} (he:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀ N (interior:m+1<N) per (y:∀i,R.family.label (d i)) (o:I→Site (R.family.side (m+1) per))
    (T:Forest ((A).levels.clock.op m per).ratio) (V:Config G (R.family.side m per))
    (c:ℂ) (χ:ℂ→L[ℝ]ℝ) (H:Config G (R.family.side (m+1) per)→ℝ),Envelope H→GaugeInvariant H→
    let B:=incident R T d o
    let θ:=((A).rep N per (m+1)).p.threshold
    let C:=cold R m per d o
    let actual (U:Config G (R.family.side (m+1) per)):=χ (c*∏i,Push.Local.primary (R.family.localSection (d i)) (o i) θ (y i) U)
    let δ:=ε*regulatorRun R.family N per (m+1)^q
    let K:=(‖χ‖*‖c‖)*(δ*originalMass R d y)
    let retained:=∫z in panel R m per d o T r,
      WilsonCoherentRetainedDriver.value R interior grade T B V z * H (state T B z) *
        χ (c*polynomial T B R d θ y o (q+2*reserve R d) z) ∂law P r T B
    |actualAverage R.family (N:=N) (C.indicator (fun U=>H U*actual U)) V-retained|≤
      δ*actualAverage R.family (N:=N) (C.indicator (fun U=>|H U*actual U|)) V+
      (2*K)*actualAverage R.family (N:=N) (C.indicator (fun U=>|H U|)) V := by
  filter_upwards [WilsonCoherentMeasuredChart.observed R simple slow J clear P hp pr sr d,
    on_event R d simple,WilsonCoherentMeasuredStencil.purchased R d simple slow J clear P pr sr q he,
    WilsonCoherentRetainedDriver.purchased R simple marks fees slow d q grade order he]
    with m chart same stencil driver N interior per y o T V c χ H eH gH
  intro B θ C actual δ K retained
  let s:=panel R m per d o T r
  let μ:=law P r T B
  let w:=actualConditionalDensity R.family N per m V
  let U:=state (G:=G) T B
  let t:=WilsonCoherentRetainedDriver.value R interior grade T B V
  let f:=mark R d o θ y c χ
  let a (z:Sample T B G):=χ (c*polynomial T B R d θ y o (q+2*reserve R d) z)
  letI : IsFiniteMeasure μ:=funded P r T B hp pr sr
  have ms:MeasurableSet s:=measurable_panel R m per d o T r
  have mu:Measurable U:=measurable_state T B
  obtain ⟨ef,gf⟩:=legitimate R d o θ y c χ
  have ew:Envelope w:=WilsonCoherentMeasuredChart.driver R m per N interior.le V
  have load:Envelope (fun u=>H u*f u):=eH.mul ef
  have absEnv (Z:Config G (R.family.side (m+1) per)→ℝ) (e:Envelope Z):Envelope (fun u=>|Z u|):=
    ⟨e.meas.abs,e.cost.imp fun _ b u=>by simpa only [Real.norm_eq_abs,abs_abs] using b u⟩
  have pulled (Z:Config G (R.family.side (m+1) per)→ℝ) (e:Envelope Z) : Envelope (Z∘U):=
    ⟨e.meas.comp mu,e.cost.imp fun _ b z=>b (U z)⟩
  have hg:GaugeInvariant (fun u=>H u*f u):=fun b u=>congrArg₂ (·*·) (gH b u) (gf b u)
  have hs (u) (hu:u∈C):actual u=f u:=
    congrArg (fun x:ℂ=>χ (c*x)) (same N per interior.le o y u hu).symm
  have swap (D:ℝ→ℝ) : C.indicator (fun u=>D (H u*actual u))=C.indicator (fun u=>D (H u*f u)):=by
    funext u
    by_cases hu:u∈C
    · rw [indicator_of_mem hu,indicator_of_mem hu,hs u hu]
    · rw [indicator_of_notMem hu,indicator_of_notMem hu]
  have first:=chart N interior.le per o T V (fun u=>H u*f u) load hg
  have joint:=chart N interior.le per o T V (fun u=>|H u*f u|) (absEnv _ load) (fun b u=>congrArg abs (hg b u))
  have last:=chart N interior.le per o T V (fun u=>|H u|) (absEnv _ eH) (fun b u=>congrArg abs (gH b u))
  have ma:Measurable a:=χ.continuous.measurable.comp ((measurable_polynomial T B R d θ y o (q+2*reserve R d)).const_mul c)
  obtain ⟨mt,change⟩:=driver N interior per o T V
  have bound:∀ᵐ z ∂μ.restrict s,0≤w (U z) ∧ 0≤t z ∧ t z≤2*w (U z) ∧ |w (U z)-t z|≤δ*w (U z) ∧
      |f (U z)-a z|≤K:=by
    filter_upwards [ae_restrict_mem ms] with z hz
    have ht:=change z
    exact ⟨actualConditionalDensity_nonneg R.family R.makes interior.le V _,ht.2.1,ht.2.2.1,ht.2.2.2,
      stencil N per interior.le y o T c χ z hz.1 hz.2⟩
  have sold:=WilsonCoherentRetainedIntegral.comparison (μ:=μ.restrict s) (w:=w∘U) (t:=t) (H:=H∘U) (F:=f∘U) (P:=a)
    ((pulled _ ((ew.mul eH).mul ef)).integrable _) ((pulled _ (ew.mul (absEnv _ eH))).integrable _)
    ((mt.mul (eH.meas.comp mu)).mul ma).aestronglyMeasurable bound
  have eq:=swap id
  simp only [id_eq] at eq
  rw [eq,swap abs,first,joint,last]
  simpa only [retained,w,t,U,s,μ,f,a,Function.comp_apply,mul_assoc] using sold

end YM.Integration.WilsonCoherentRetainedExperiment
