import YM.Integration.WilsonLocalCompactWindowInvoice
import YM.Integration.WilsonLocalCompactObservation

/-! The source at an independently chosen intermediate date is compared on its
own full Wilson marginal and every earlier held field with one before-radius price. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactSegmentMean
open Filter Finset MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension OPE OPE.Log Trace.Pilot
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLocalCompactHistory
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I] (R:Run G)

theorem original (simple:G.Simple) (pace:WilsonWindowReportingPace.Slow R.kit)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (d:I→ℕ) {B:ℕ} (bp:0<B) (q grade:ℕ) (ord:q+7≤grade) {ε:ℝ} (ep:0<ε):
    ∀ᶠr:ℝ in trail,let j:=WilsonCloseCaptureDate.level R.family.S r
    let b:=WilsonMeasuredWindow.stop R.family.path.levels simple B r
    j≤b ∧ ∀k l:ℕ,j≤k→∀live:k≤l,l≤b→∀N:ℕ,b≤N→∀(interior:l<N) per
      (T:∀i,i<l→Forest (R.family.path.levels.clock.op i per).ratio)
      (o:∀i,i<l→I→Site (R.family.side (i+1) per))
      (H:Config G (R.family.side l per)→ℝ),Envelope H→GaugeInvariant H→
    let v:=program R interior grade d T o H live
    let f:=actualTransport R.family (N:=N) H live
    let τ:=ε*regulatorRun R.family N per b^q
    Envelope v ∧ (∀V,|v V-f V|≤τ*actualTransport R.family (N:=N) (fun U=>|H U|) live V) ∧
    (∀u (past:u≤k) W,|actualTransport R.family (N:=N) v past W-
       actualTransport R.family (N:=N) H (past.trans live) W|≤
       τ*actualTransport R.family (N:=N) (fun U=>|H U|) (past.trans live) W) ∧
    (∫ V,|v V-f V| ∂scene R.family.path N per k)≤
       τ*(∫ U,|H U| ∂scene R.family.path N per l):=by
  obtain ⟨η,hη,invoice⟩:=WilsonLocalCompactWindowInvoice.original R simple pace bp q ep
  obtain ⟨c,bank⟩:=eventually_atTop.1 (WilsonLocalCompactHistoryMean.original R simple marks fees pace.2 d (q+2) grade (by omega) hη)
  filter_upwards [invoice,(WilsonCloseCaptureDate.height R).grows.eventually_ge_atTop c] with r paid ready
  intro j b
  refine ⟨paid.1,?_⟩
  intro k l jk live lb N bn interior per T o H eh gh v f τ
  have recv:=bank k (ready.trans jk) l live N interior per T o H eh gh
  have mean:∀V,|v V-f V|≤τ*actualTransport R.family (N:=N) (fun U=>|H U|) live V:=fun V=>
    (recv.2.2 V).trans (mul_le_mul_of_nonneg_right (paid.2 N bn per k l jk lb)
      ((abs_nonneg _).trans (recv.2.1 V)))
  have obs:=WilsonLocalCompactObservation.tested R interior.le live eh recv.1 τ mean
  exact ⟨recv.1,mean,obs.1,obs.2.1⟩

end YM.Integration.WilsonLocalCompactSegmentMean
