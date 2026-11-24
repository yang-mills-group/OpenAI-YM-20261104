import YM.Integration.WilsonCloseCaptureSignedPrice
import YM.Integration.WilsonCloseCaptureDate
import YM.RG05Readout.Harvest.Spec
import YM.RG05Readout.Chalice.Choir

/-! Simultaneous normalized physical field bills, finite observation levels, and fitted reference dates on the one funded Wilson history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCloseCaptureCalendar
open Filter Lattice RG Source Labels OPE OPE.Log Trace.Pilot PhysicalNext.Repeat.Legato Bandage
open WilsonLimitConstruction RG05Readout Many Halls Records Chalice Address Native
open scoped Classical Topology
universe u
variable {G : Gauge} (R : Run G) (hG : G.Simple)

def lower (r : ℝ) : ℕ := WilsonCloseCaptureDate.level R.family.S r-1
def reported (K : ℕ) (r : ℝ) : ℕ := WilsonMeasuredWindow.stop R.family.path.levels hG K r

theorem dates (slow : WilsonWindowReportingPace.Slow R.kit) {K : ℕ} (large : 4<K) :
    Height R.family.S trail LogV (lower R) 1 ∧ Height R.family.S trail LogV (reported R hG K) 1 ∧
    ∀ᶠ r in trail, lower R r+1 = WilsonCloseCaptureDate.level R.family.S r ∧
      lower R r+1 < reported R hG K r ∧ CaptureW R.family (lower R r+1) (reported R hG K r) r K := by
  have hk : 0<K := by omega
  have depth := WilsonCloseCaptureDate.height R
  have actual := WilsonFundedMeasuredWindow.all_radii R slow hG hk
  refine ⟨Log.previous PhysMS.to_log_zoom depth R.family.path.levels.fits.mesh,
    WilsonMeasuredWindow.measured_stop_height _ hG K (WilsonFundedMeasuredWindow.paced R slow) hk
      PhysMS.to_log_zoom PhysMS.length_rate,?_⟩
  have late := (PhysMS.length_rate.tends neg_one_lt_zero PhysMS.to_log_zoom).eventually
    (gt_mem_nhds (R.family.S.a_pos 0))
  filter_upwards [PhysMS.length_rate.pos,late,depth.grows.eventually_ge_atTop 1] with r rp rs first
  change 0 < r at rp
  have same : lower R r+1 = WilsonCloseCaptureDate.level R.family.S r := Nat.sub_add_cancel first
  obtain ⟨step,left,right,_,_,_⟩ := WilsonCloseCaptureDate.window R slow hG hk rp rs.le
  refine ⟨same, same.symm ▸ step,same.symm ▸ ⟨?_,right,left⟩⟩
  obtain ⟨lo,hi⟩ := actual.2 r rp rs.le
  have apos := R.family.S.a_pos (reported R hG K r)
  change RG05Readout.measured R.family.path.levels (reported R hG K r) r K
  unfold RG05Readout.measured
  rw [Real.rpow_natCast,show (K:ℝ)+1 = (K+1:ℕ) by push_cast; rfl, Real.rpow_natCast]
  change R.family.S.a (reported R hG K r) * RG16.Lambda R.family.path.levels (reported R hG K r) ^ K ≤ r ∧
    r ≤ R.family.S.a (reported R hG K r) * RG16.Lambda R.family.path.levels (reported R hG K r) ^ (K+1)
  constructor
  · rw [mul_comm]; exact (le_div_iff₀ apos).mp lo
  · rw [mul_comm]; exact (div_le_iff₀ apos).mp hi

structure Funding where
  allowance : ℕ → ℕ → ℝ
  start : ℕ → ℕ
  basis : ∀ d : ℕ, Push.RelayDifference.Cutoffs → Emblems R.family d
  rows : Anchored R.doors allowance R.makes start basis
  dates (j t ℓ d : ℕ) :
    (∀ᶠ b:ℕ in atTop, (∀ i, b ≤ i → Shadow.Pin R.family i d) ∧
      Stock.Tabs.opens R.family.path.levels (bumper (2*t)) j b ∧ Address.Awake (C:=R.family) R.doors allowance b d) ∧
      ∃ k,∀ᶠ n:ℕ in atTop, Warm R.family n (ℓ+1) k

theorem original {T : Campaign R} (W : Campaign.Pillars R T) {δ : ℝ}
    (fund : FundedOriginalProperties.{u} hG δ W)
    (book : OPE.Package R.family R.w (mutt R.family.path.levels R.Q) R.doors) : Nonempty (Funding R) := by
  obtain ⟨storage,_⟩ := WilsonCloseCaptureFinances.original R hG W fund
  have signed := WilsonCloseCaptureSignedPrice.purchased R hG fund.2.2.2.2.2.2.1
  obtain ⟨B,accounts⟩ := Harvest.elder book storage hG signed
  choose start paid using fun d:ℕ => ((accounts 0 0 0 d).1.mono (fun _ h => h.2.2)).exists
  obtain ⟨Y,rows⟩ := Chalice.opening R.makes start paid
  exact ⟨⟨B,start,Y,rows,accounts⟩⟩

end YM.Integration.WilsonCloseCaptureCalendar
