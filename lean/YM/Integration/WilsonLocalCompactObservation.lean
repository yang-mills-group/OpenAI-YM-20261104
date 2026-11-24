import YM.Integration.WilsonLocalCompactCaptureMean
import YM.Integration.ActualScalarTransport

/-! Read the whole compact capture comparison at every earlier physical
configuration and in the unchanged normalized Wilson marginal. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactObservation
open Filter Set MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension
open OPE OPE.Log Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLocalCompactHistory
open scoped Classical Topology
variable {G:Gauge} (R:Run G) {N per j b:ℕ}

private theorem abs_envelope {X:Type} [MeasurableSpace X] {h:X→ℝ} (e:Envelope h):Envelope (fun x=>|h x|):=
  ⟨e.meas.abs,e.cost.choose,fun x=>by simpa only [Real.norm_eq_abs,abs_abs] using e.cost.choose_spec x⟩

private theorem integr {h:Config G (R.family.side j per)→ℝ} (live:j≤N) (e:Envelope h):
    Integrable h (scene R.family.path N per j):=by
  have base:=actualTransport_weighted_integrable R.family R.makes live (e.meas.aestronglyMeasurable (μ:=prior G _)) e.cost.choose_spec le_rfl
  rw [actualTransport_base R.family R.makes live] at base
  exact actualScene_integrable_of_weighted R.family R.makes live base

theorem tested (top:b≤N) (live:j≤b) {H:Config G (R.family.side b per)→ℝ} (eh:Envelope H)
    {v:Config G (R.family.side j per)→ℝ} (ev:Envelope v) (τ:ℝ)
    (small:∀V,|v V-actualTransport R.family (N:=N) H live V|≤τ*actualTransport R.family (N:=N) (fun U=>|H U|) live V):
    let f:=actualTransport R.family (N:=N) H live;let A:=actualTransport R.family (N:=N) (fun U=>|H U|) live
    let μ:=scene R.family.path N per j
    (∀u (past:u≤j) W,|actualTransport R.family (N:=N) v past W-actualTransport R.family (N:=N) H (past.trans live) W|≤
      τ*actualTransport R.family (N:=N) (fun U=>|H U|) (past.trans live) W) ∧
    (∫V,|v V-f V| ∂μ)≤τ*∫U,|H U| ∂scene R.family.path N per b ∧
    ∀L:Config G (R.family.side j per)→ℝ,Envelope L→(∫V,|L V| * |v V-f V| ∂μ)≤τ*∫V,|L V| * A V ∂μ:=by
  intro f A μ
  let J:=fun U=>|H U|
  have ej:Envelope J:=abs_envelope eh
  have ea:Envelope A:=WilsonCoherentEarlier.envelope R.family R.makes top ej live
  have ef:Envelope f:=WilsonCoherentEarlier.envelope R.family R.makes top eh live
  have diff:Envelope (fun V=>|v V-f V|):=abs_envelope (by simpa only [sub_eq_add_neg] using ev.add ef.neg)
  have jN:=live.trans top
  have weighted:=actualTransport_weighted_integrable R.family R.makes top (ej.meas.aestronglyMeasurable (μ:=prior G _)) ej.cost.choose_spec le_rfl
  rw [actualTransport_base R.family R.makes top] at weighted
  have ren: (∫V,A V ∂μ)=(∫U,J U ∂scene R.family.path N per b):=actualScene_transport R.family R.makes top weighted live
  refine ⟨fun u past W=>?_,?_,fun L el=>?_⟩
  · have later:=WilsonCoherentEarlier.signed R.family R.makes jN ev ef ea ea (x:=τ) (y:=0)
      (fun V=>by simpa only [zero_mul,add_zero] using small V) past W
    simpa only [f,A,actualTransport_tower R.family R.makes top H live past,actualTransport_tower R.family R.makes top (fun U=>|H U|) live past,zero_mul,add_zero] using later
  · rw [←ren,←integral_const_mul]
    exact integral_mono (integr R jN diff) ((integr R jN ea).const_mul _) small
  · rw [←integral_const_mul]
    exact integral_mono (integr R jN ((abs_envelope el).mul diff)) ((integr R jN ((abs_envelope el).mul ea)).const_mul _) fun V=>by
      calc |L V| * |v V-f V|≤|L V| * (τ*A V):=mul_le_mul_of_nonneg_left (small V) (abs_nonneg _)
        _=τ*(|L V| * A V):=by ring

variable {I:Type} [Fintype I]

theorem original (simple:G.Simple) (pace:WilsonWindowReportingPace.Slow R.kit)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (d:I→ℕ) {B:ℕ} (bp:0<B) (q grade:ℕ) (ord:q+7≤grade) {ε:ℝ} (ep:0<ε):
    ∀ᶠr:ℝ in trail,let j:=WilsonCloseCaptureDate.level R.family.S r
    let b:=WilsonMeasuredWindow.stop R.family.path.levels simple B r
    ∃live:j≤b,∀N (top:b<N) per
      (T:∀i,i<b→Forest (R.family.path.levels.clock.op i per).ratio)
      (o:∀i,i<b→I→Site (R.family.side (i+1) per))
      (H:Config G (R.family.side b per)→ℝ),Envelope H→GaugeInvariant H→
    let v:=program R top grade d T o H live;let f:=actualTransport R.family (N:=N) H live
    let A:=actualTransport R.family (N:=N) (fun U=>|H U|) live
    let μ:=scene R.family.path N per j;let τ:=ε*regulatorRun R.family N per b^q
    (∀u (past:u≤j) W,|actualTransport R.family (N:=N) v past W-actualTransport R.family (N:=N) H (past.trans live) W|≤
      τ*actualTransport R.family (N:=N) (fun U=>|H U|) (past.trans live) W) ∧
    (∫V,|v V-f V| ∂μ)≤τ*∫U,|H U| ∂scene R.family.path N per b ∧
    ∀L:Config G (R.family.side j per)→ℝ,Envelope L→(∫V,|L V| * |v V-f V| ∂μ)≤τ*∫V,|L V| * A V ∂μ:=by
  filter_upwards [WilsonLocalCompactCaptureMean.original R simple pace marks fees d bp q grade ord ep] with r bank
  obtain ⟨live,issued⟩:=bank
  refine ⟨live,fun N top per T o H eh gh=>?_⟩
  have receipt:=issued N top per T o H eh gh
  exact tested R top.le live eh receipt.1 _ receipt.2.2

end YM.Integration.WilsonLocalCompactObservation
