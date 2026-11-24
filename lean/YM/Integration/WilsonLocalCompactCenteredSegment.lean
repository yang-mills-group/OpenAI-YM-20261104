import YM.Integration.WilsonLocalCompactShifts

/-! Any genuine short reporting interval can be tested against fluctuations
around its conditional mean, including after passage to an earlier held field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactCenteredSegment
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
    Envelope v ∧
    (∀V c,|v V-f V|≤τ*actualTransport R.family (N:=N) (fun U=>|H U-c|) live V) ∧
    (∀u (past:u≤k) W c,|actualTransport R.family (N:=N) v past W-
       actualTransport R.family (N:=N) H (past.trans live) W|≤
       τ*actualTransport R.family (N:=N) (fun U=>|H U-c|) (past.trans live) W) ∧
    ∀c:ℝ,(∫ V,|v V-f V| ∂scene R.family.path N per k)≤
       τ*(∫ U,|H U-c| ∂scene R.family.path N per l):=by
  obtain ⟨s,normalized⟩:=eventually_atTop.1
    (WilsonLocalCompactShifts.funded R simple marks fees pace.2 d grade (by omega))
  filter_upwards [WilsonLocalCompactSegmentMean.original R simple pace marks fees d bp q grade ord ep,
    (WilsonCloseCaptureDate.height R).grows.eventually_ge_atTop s] with r paid ready
  intro j b
  refine ⟨paid.1,?_⟩
  intro k l jk live lb N bn interior per T o H eh gh v f τ
  have P {i} (hi:i≤l) (ji:j ≤ i):=paid.2 i l ji hi lb N bn interior per T o H eh gh
  have shifted (c:ℝ):program R interior grade d T o (fun U=>H U-c) live=fun V=>v V-c:=by
    change program R interior grade d T o (fun U=>H U-c) live=fun V=>program R interior grade d T o H live V-c
    induction live using Nat.decreasingInduction with
    | self=>rw [start,start]
    | of_succ i hi ih=>
      rw [step R _ _ _ _ _ _ hi,step R _ _ _ _ _ H hi,ih (jk.trans (Nat.le_succ _))]
      exact normalized i (ready.trans jk) N ((Nat.succ_le_of_lt hi).trans_lt interior) per (o i hi) (T i hi) _
        (P hi (jk.trans (Nat.le_succ _))).1 c
  have reality (c:ℝ):actualTransport R.family (N:=N) (fun U=>H U-c) live=fun V=>f V-c:=
    WilsonLocalCompactShifts.actual R.family R.makes interior.le eh c live
  have centered (c:ℝ):GaugeInvariant (fun U=>H U-c):=fun a U=>congrArg (fun z=>z-c) (gh a U)
  have test (c:ℝ):=paid.2 k l jk live lb N bn interior per T o (fun U=>H U-c)
    (WilsonLocalCompactShifts.bounded eh c) (centered c)
  have ev:Envelope v:=(P live jk).1
  refine ⟨ev,fun V c=>?_,fun u past W c=>?_,fun c=>?_⟩
  · have bound:=(test c).2.1 V
    rw [shifted c,reality c] at bound
    simpa only [sub_sub_sub_cancel_right] using bound
  · have bound:=(test c).2.2.1 u past W
    rw [shifted c,WilsonLocalCompactShifts.actual R.family R.makes (live.trans interior.le) ev c past,
      WilsonLocalCompactShifts.actual R.family R.makes interior.le eh c (past.trans live)] at bound
    simpa only [sub_sub_sub_cancel_right] using bound
  · have bound:=(test c).2.2.2
    rw [shifted c,reality c] at bound
    simpa only [sub_sub_sub_cancel_right] using bound

end YM.Integration.WilsonLocalCompactCenteredSegment
