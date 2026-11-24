import YM.Integration.WilsonLocalCompactCaptureMean

/-! One physical date and coupling budget supports every contained interval,
including an interior subinterval when the reporting date is the cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactWindowInvoice
open Filter Finset Lattice RG Wilson RG16 Precision OPE OPE.Log Trace.Pilot PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
theorem original (simple:G.Simple) (pace:WilsonWindowReportingPace.Slow R.kit) {B:ℕ} (bp:0<B)
    (q:ℕ) {ε:ℝ} (ep:0<ε):
    ∃η:ℝ,0<η ∧ ∀ᶠr:ℝ in trail,let j:=WilsonCloseCaptureDate.level R.family.S r
    let b:=WilsonMeasuredWindow.stop R.family.path.levels simple B r
    j≤b ∧ ∀N:ℕ,b≤N→∀per:ℕ,let g:=regulatorRun R.family N per
    let δ:=fun i=>η*g (i+1)^(q+2)
    ∀k l:ℕ,j≤k→l≤b→Real.exp (∑i∈Ico k l,2*(δ i*(1+δ i)))-1≤ε*g b^q:=by
  let B':ℝ:=(B+2:ℕ)
  have hB:0<B':=by dsimp [B'];positivity
  let θ:=min 1 (ε/2)
  have θp:0<θ:=lt_min zero_lt_one (half_pos ep)
  obtain ⟨η,hη,refund⟩:=WilsonLocalCompactRate.summed hB θp q
  refine ⟨η,hη,?_⟩
  have upper:=WilsonMeasuredWindow.measured_stop_height _ simple B (WilsonFundedMeasuredWindow.paced R pace)
    bp PhysMS.to_log_zoom PhysMS.length_rate
  have late:=(PhysMS.length_rate.tends neg_one_lt_zero PhysMS.to_log_zoom).eventually (gt_mem_nhds (R.family.S.a_pos 0))
  filter_upwards [PhysMS.length_rate.pos,late,upper.grows.eventually (WilsonLocalCompactClock.prices R simple hB)] with r rp rs invoice
  intro j b
  have window:=WilsonCloseCaptureDate.window R pace simple bp (r:=r) rp rs.le
  have fit:j≤b:=window.1.le
  refine ⟨fit,fun N top per=>?_⟩
  intro g δ k l jk lb
  let D:=fun i=>2*(δ i*(1+δ i))
  let S:=∑i∈Ico k l,D i
  have gp (i):0≤g i:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have dp (i):0≤D i:=by
    have buy:0≤δ i:=mul_nonneg hη.le (pow_nonneg (gp _) _)
    dsimp only [D];positivity
  have funds:=invoice j fit window.2.2.2.2.2 N top per
  have paid:=refund j b g _ 1 (by norm_num) (gp b) funds.1 funds.2.1 (fun i hi=>by
    rw [mem_Ico] at hi
    exact ⟨gp _,funds.2.2 (i+1) (hi.1.trans (Nat.le_succ i)) hi.2⟩)
  have full:(∑i∈Ico j b,D i)≤θ*g b^q:=by simpa only [D,δ,mul_one] using paid
  have subset:Ico k l⊆Ico j b:=by
    intro i hi;rw [mem_Ico] at hi ⊢;exact ⟨jk.trans hi.1,hi.2.trans_le lb⟩
  have budget:S≤θ*g b^q:=(sum_le_sum_of_subset_of_nonneg subset (fun i _ _=>dp i)).trans full
  have sp:0≤S:=sum_nonneg (fun i _=>dp i)
  have cap:S≤1:=calc
    S≤θ*g b^q:=budget
    _≤θ*1:=mul_le_mul_of_nonneg_left (pow_le_one₀ (gp _) (funds.2.2 b fit le_rfl).1) θp.le
    _≤1:=by simpa only [mul_one] using (min_le_left 1 (ε/2))
  have lim:=Real.abs_exp_sub_one_le (x:=S) (by rw [abs_of_nonneg sp];exact cap)
  rw [abs_of_nonneg sp] at lim
  have two:2*θ≤ε:=by linarith only [show θ≤ε/2 from min_le_right ..]
  calc Real.exp S-1≤|Real.exp S-1|:=le_abs_self _
    _≤2*S:=lim
    _≤2*(θ*g b^q):=mul_le_mul_of_nonneg_left budget (by norm_num)
    _≤ε*g b^q:=by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right two (pow_nonneg (gp b) _)

end YM.Integration.WilsonLocalCompactWindowInvoice
