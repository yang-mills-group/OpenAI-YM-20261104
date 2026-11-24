import YM.Integration.WilsonLocalCompactCapture
import YM.Integration.WilsonLocalCompactHistoryMean

/-! The complete signed residual over the capture interval is paid by the
actual conditional first moment of the originally submitted observable. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactCaptureMean
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
    let v:=program R top grade d T o H live
    let F:=actualTransport R.family (N:=N) H live
    let A:=actualTransport R.family (N:=N) (fun U=>|H U|) live
    Envelope v ∧ (∀V,|F V|≤A V) ∧ ∀V,|v V-F V|≤ε*regulatorRun R.family N per b^q*A V := by
  let B':ℝ:=(B+2:ℕ)
  have hB:0<B':=by dsimp [B'];positivity
  let θ:=min 1 (ε/2)
  have θp:0<θ:=lt_min zero_lt_one (half_pos ep)
  obtain ⟨η,hη,refund⟩:=WilsonLocalCompactRate.summed hB θp q
  have bank:=WilsonLocalCompactHistoryMean.original R simple marks fees pace.2 d (q+2) grade (by omega) hη
  have lower:=WilsonCloseCaptureDate.height R
  have upper:=WilsonMeasuredWindow.measured_stop_height _ simple B (WilsonFundedMeasuredWindow.paced R pace)
    bp PhysMS.to_log_zoom PhysMS.length_rate
  have late:=(PhysMS.length_rate.tends neg_one_lt_zero PhysMS.to_log_zoom).eventually (gt_mem_nhds (R.family.S.a_pos 0))
  filter_upwards [PhysMS.length_rate.pos,late,lower.grows.eventually bank,
    upper.grows.eventually (WilsonLocalCompactClock.prices R simple hB)] with r rp rs owned invoice
  intro j b
  have window:=WilsonCloseCaptureDate.window R pace simple bp (r:=r) rp rs.le
  have fit:j≤b:=window.1.le
  refine ⟨fit,fun N top per T o H eh gh=>?_⟩
  let g:=regulatorRun R.family N per
  have funds:=invoice j fit window.2.2.2.2.2 N top.le per
  have cutoff:=owned b fit N top per T o H eh gh
  let δ:=fun i=>η*g (i+1)^(q+2)
  let D:=fun i=>2*(δ i*(1+δ i))
  let S:=∑i∈Finset.Ico j b,D i
  have gp (i):0≤g i:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have paid:=refund j b g _ 1 (by norm_num) (gp b) funds.1 funds.2.1 (fun i hi=>by
    rw [Finset.mem_Ico] at hi
    exact ⟨gp _,funds.2.2 (i+1) (hi.1.trans (Nat.le_succ i)) hi.2⟩)
  have budget:S≤θ*g b^q:=by simpa only [S,D,δ,mul_one] using paid
  have sp:0≤S:=Finset.sum_nonneg (fun i _=>by
    have dp:0≤δ i:=mul_nonneg hη.le (pow_nonneg (gp _) _)
    dsimp only [D];positivity)
  have cap:S≤1:=calc
    S≤θ*g b^q:=budget
    _≤θ*1:=mul_le_mul_of_nonneg_left (pow_le_one₀ (gp _) (funds.2.2 b fit le_rfl).1) θp.le
    _≤1:=by simpa only [mul_one] using (min_le_left 1 (ε/2))
  have lim:=Real.abs_exp_sub_one_le (x:=S) (by rw [abs_of_nonneg sp];exact cap)
  rw [abs_of_nonneg sp] at lim
  have two:2*θ≤ε:=by linarith only [show θ≤ε/2 from min_le_right ..]
  have sum:Real.exp S-1≤ε*g b^q:=calc
    Real.exp S-1≤|Real.exp S-1|:=le_abs_self _
    _≤2*S:=lim
    _≤2*(θ*g b^q):=mul_le_mul_of_nonneg_left budget (by norm_num)
    _≤ε*g b^q:=by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right two (pow_nonneg (gp b) _)
  exact ⟨cutoff.1,cutoff.2.1,fun V=>(cutoff.2.2 V).trans (mul_le_mul_of_nonneg_right sum ((abs_nonneg _).trans (cutoff.2.1 V)))⟩

end YM.Integration.WilsonLocalCompactCaptureMean
