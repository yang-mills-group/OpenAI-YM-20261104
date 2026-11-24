import YM.Integration.WilsonLocalCompactClock
import YM.Integration.WilsonLocalCompactRate

/-! Physical replacement of the entire compact old action across the
prescribed capture interval, with a price independent of its upper regulator. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactCapture
open Filter Lattice RG Wilson Tree RG16 Precision PertExtension
open OPE OPE.Log Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
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
    ∃live:j≤b,∀N (top:b<N) per
      (T:∀i,i<b→Forest (R.family.path.levels.clock.op i per).ratio)
      (o:∀i,i<b→I→Site (R.family.side (i+1) per))
      (H:Config G (R.family.side b per)→ℝ),Envelope H→GaugeInvariant H→
    ∀C:ℝ,(∀U,|H U|≤C)→
    let v:=program R top grade d T o H live
    let F:=actualTransport R.family (N:=N) H live
    Envelope v ∧ ∀V,|v V-F V|≤ε*regulatorRun R.family N per b^q*C := by
  let B':ℝ:=(B+2:ℕ)
  have hB:0<B':=by dsimp [B'];positivity
  obtain ⟨η,hη,refund⟩:=WilsonLocalCompactRate.summed hB ep q
  have bank:=WilsonLocalCompactHistory.original R simple marks fees pace.2 d (q+2) grade (by omega) hη
  have lower:=WilsonCloseCaptureDate.height R
  have upper:=WilsonMeasuredWindow.measured_stop_height _ simple B (WilsonFundedMeasuredWindow.paced R pace)
    bp PhysMS.to_log_zoom PhysMS.length_rate
  have late:=(PhysMS.length_rate.tends neg_one_lt_zero PhysMS.to_log_zoom).eventually (gt_mem_nhds (R.family.S.a_pos 0))
  filter_upwards [PhysMS.length_rate.pos,late,lower.grows.eventually bank,
    upper.grows.eventually (WilsonLocalCompactClock.prices R simple hB)] with r rp rs owned invoice
  intro j b
  have window:=WilsonCloseCaptureDate.window R pace simple bp (r:=r) rp rs.le
  have fit:j≤b:=window.1.le
  refine ⟨fit,fun N top per T o H eh gh C bound=>?_⟩
  let g:=regulatorRun R.family N per
  have funds:=invoice j fit window.2.2.2.2.2 N top.le per
  have cutoff:=owned b fit N top per T o H eh gh C bound
  have cp:0≤C:=(abs_nonneg _).trans (bound 1)
  have gp (i):0≤g i:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have paid:=refund j b g _ C cp (gp b) funds.1 funds.2.1 (fun i hi=>by
    rw [Finset.mem_Ico] at hi
    exact ⟨gp _,funds.2.2 (i+1) (hi.1.trans (Nat.le_succ i)) hi.2⟩)
  exact ⟨cutoff.1,fun V=>(cutoff.2 V).trans paid⟩

end YM.Integration.WilsonLocalCompactCapture
