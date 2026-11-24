import YM.Integration.WilsonRegisteredPreviousObservable
import YM.Integration.WilsonRegisteredAngularGate
import YM.Integration.WilsonCoherentRetainedExperiment

/-! Signed measurement of the genuine old angular polynomial under the
original finite conditional. The second signed field stays in the same
sample, and the density uses both physical fibre masses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredFrozenConditional
open Function Filter Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm
open RG16 ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction Pert.Asymptotics
open WilsonReportingForestPivots WilsonCoherentForestMeasure WilsonCoherentForestReadout
open WilsonInheritedRegisteredField WilsonRegisteredAffineSource WilsonRegisteredAngularGate
open scoped Classical Topology
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]
local notation "A" => R.family.path

theorem measured (simple:G.Simple) (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A).levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) (hp:LocalRatio P) {r:ℝ}
    (pr:0<r) (sr:r<Chart.small G P) (jr:r≤J.r) (d:I→ℕ) (p grade:ℕ) (order:p+5≤grade) {ε:ℝ} (he:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀ N (interior:m+1<N) per (o:I→Site (R.family.side (m+1) per))
    (T:Forest ((A).levels.clock.op m per).ratio) (V:Config G (R.family.side m per))
    (h:ℕ) (_ref:R.family.ref h ≤ m+1) (v:R.family.label h) (x:Site (R.family.side (m+1) per))
    (b H q:ℕ) (η:ℂ→L[ℝ]ℝ) (G':Config G (R.family.side (m+1) per)→ℝ), Envelope G'→GaugeInvariant G'→
    let k:=m+1
    let Q:=(A).rep N per k
    let Z:=packet R.makes interior.le v x
    let B:=incident R T d o
    let F:=fun U=>η (WilsonRegisteredFrozenReading.previous R interior.le v x b U)
    let s:=strip R m per d o x H T r
    let C:=cold R m per d o ∩ screen R m per o x H
    let K:=‖η‖*((R.family.path.levels.params k).columns*(R.family.labels.level h).coeffSize
        ((R.family.labels.level h).core Z.x)*((width R N per k)^(q+1)/q.factorial))
    let δ:=ε*regulatorRun R.family N per k^p
    let expected:=∫z in s,WilsonCoherentRetainedDriver.value R interior grade T B V z*
      G' (state T B z)*WilsonRegisteredFrozenReading.reading R interior.le v x b q T B η z ∂law P r T B
    b*(4*Q.p.B+2)+2*Q.p.B ≤ H→q+1 ≤ Q.p.order→
    |actualAverage R.family (N:=N) (C.indicator (fun U=>G' U*F U)) V-expected| ≤
      δ*actualAverage R.family (N:=N) (C.indicator (fun U=>|G' U*F U|)) V+
        (2*K)*actualAverage R.family (N:=N) (C.indicator (fun U=>|G' U|)) V := by
  filter_upwards [WilsonRegisteredAngularGate.physical R simple slow J clear P hp pr sr d,
    WilsonRegisteredAngularGate.radius R simple slow J clear d jr,
    WilsonRegisteredFrozenReading.original R simple,
    WilsonCoherentRetainedDriver.purchased R simple marks fees slow d p grade order he] with m chart angles probe driver
  intro N interior per o T V h ref v x b H q η G' eH gH k Q Z B F s C K δ expected range active
  let μ:=law P r T B
  let U:=state (G:=G) T B
  let w:=actualConditionalDensity R.family N per m V
  let t:=WilsonCoherentRetainedDriver.value R interior grade T B V
  let a:=WilsonRegisteredFrozenReading.reading R interior.le v x b q T B η
  letI:IsFiniteMeasure μ:=funded P r T B hp pr sr
  have ms:MeasurableSet s:=measurable_strip R m per d o x H T r
  have mu:Measurable U:=measurable_state T B
  have ew:Envelope w:=WilsonCoherentMeasuredChart.driver R m per N interior.le V
  obtain ⟨ef,gf⟩:=WilsonRegisteredPreviousObservable.original R interior.le ref v x b η
  have load:Envelope (fun u=>G' u*F u):=eH.mul ef
  have Fg:GaugeInvariant (fun u=>G' u*F u):=fun a u=>congrArg₂ (·*·) (gH a u) (gf a u)
  have aeH (Z:Config G (R.family.side k per)→ℝ) (e:Envelope Z):Envelope (fun u=>|Z u|):=
    ⟨e.meas.abs,e.cost.imp fun _ cap u=>by simpa only [Real.norm_eq_abs,abs_abs] using cap u⟩
  have pulled (Z:Config G (R.family.side k per)→ℝ) (e:Envelope Z):Envelope (Z∘U):=
    ⟨e.meas.comp mu,e.cost.imp fun _ cap z=>cap (U z)⟩
  have first:=chart N interior.le per o x H T V (fun u=>G' u*F u) load Fg
  have joint:=chart N interior.le per o x H T V (fun u=>|G' u*F u|) (aeH _ load) (fun a u=>congrArg abs (Fg a u))
  have last:=chart N interior.le per o x H T V (fun u=>|G' u|) (aeH _ eH) (fun a u=>congrArg abs (gH a u))
  have ma:Measurable a:=WilsonRegisteredFrozenReading.measured R interior.le v x b q T B η ref
  obtain ⟨mt,change⟩:=driver N interior per o T V
  have bound:∀ᵐ z ∂μ.restrict s,0≤w (U z) ∧ 0≤t z ∧ t z≤2*w (U z) ∧ |w (U z)-t z|≤δ*w (U z) ∧
      |F (U z)-a z|≤K:=by
    filter_upwards [ae_restrict_mem ms] with z hz
    have ht:=change z
    exact ⟨actualConditionalDensity_nonneg R.family R.makes interior.le V _,ht.2.1,ht.2.2.1,ht.2.2.2,
      probe N per interior.le h ref v x b H q T B η z range (angles N interior.le per o x H T z hz) active hz.2.2⟩
  have sold:=WilsonCoherentRetainedIntegral.comparison (μ:=μ.restrict s) (w:=w∘U) (t:=t) (H:=G'∘U) (F:=F∘U) (P:=a)
    ((pulled _ ((ew.mul eH).mul ef)).integrable _) ((pulled _ (ew.mul (aeH _ eH))).integrable _)
    ((mt.mul (eH.meas.comp mu)).mul ma).aestronglyMeasurable bound
  dsimp only at first joint last
  change actualAverage R.family (N:=N) (C.indicator (fun U=>G' U*F U)) V=_ at first
  change actualAverage R.family (N:=N) (C.indicator (fun U=>|G' U*F U|)) V=_ at joint
  change actualAverage R.family (N:=N) (C.indicator (fun U=>|G' U|)) V=_ at last
  rw [first,joint,last]
  simpa only [expected,w,t,U,s,μ,F,a,Function.comp_apply,mul_assoc] using sold

end YM.Integration.WilsonRegisteredFrozenConditional
end
