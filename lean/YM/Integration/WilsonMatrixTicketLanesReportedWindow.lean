import YM.Integration.WilsonFundedMeasuredWindow
import YM.Integration.WilsonMatrixTicketLanesReportedCrew

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedWindow
open Function Filter Finset Set MeasureTheory Extraction Table Next.Rank OPE RG12 RG17 SharpGram
open PhysicalNext.Repeat.Legato
open scoped Topology Classical BigOperators
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  {F : Spec.Final R.family f S}

/-- The actual stop elected with the measured position layout satisfies the spatial
window required to price all incoming grades. This uses the original reported
block schedule at each radius. -/
theorem original (L : Layout F) (hG : G.Simple) (pace : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (hB : 0 < B) (elected : L.level = WilsonMeasuredWindow.stop R.family.path.levels hG B) :
    ∀ᶠ r in RG17.home, R.family.S.a (L.level r) ≤ r ∧
      r ≤ R.family.S.a (L.level r) * R.family.path.levels.clock.hatBeta (L.level r)^2 := by
  rw [elected]
  let A := R.family.path.levels
  let m := WilsonMeasuredWindow.stop A hG B
  let f : ℝ := 3^(B+1)
  have fp : 0<f := by dsimp [f]; positivity
  have grows := Real.tendsto_log_atTop.comp (Station.hat_rate A hG)
  have cheap := ((Real.isLittleO_pow_exp_atTop (n:=B+1)).comp_tendsto grows).bound (inv_pos.mpr fp)
  have fits : ∀ᶠ k : ℕ in atTop,RG16.Lambda A k^(B+1)≤A.clock.hatBeta k := by
    filter_upwards [grows.eventually_ge_atTop 1,cheap] with k high upper
    let b := A.clock.hatBeta k
    let l := Real.log b
    have one : 1≤l := high
    have bpos : 0<b := zero_lt_one.trans (A.fits.delayed k)
    change ‖l^(B+1)‖≤f⁻¹*‖Real.exp l‖ at upper
    rw [Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans one) _),Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.exp_log bpos] at upper
    change (2+l)^(B+1)≤b
    calc
      _ ≤ (3*l)^(B+1) := pow_le_pow_left₀ (by linarith) (by linarith only [one]) _
      _ = f*l^(B+1) := mul_pow ..
      _ ≤ b := by simpa only [←mul_assoc,mul_inv_cancel₀ fp.ne',one_mul]
        using mul_le_mul_of_nonneg_left upper fp.le
  obtain ⟨ranks,window⟩ := WilsonFundedMeasuredWindow.all_radii R pace hG hB
  have short : ∀ᶠ r : ℝ in RG17.home,r<R.family.S.a 0 := (gt_mem_nhds (R.family.S.a_pos 0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [RG17.positiveLength,short,ranks.eventually fits] with r hr small upper
  have a := R.family.S.a_pos (m r)
  have price := window r hr small.le
  have Bx := A.fits.delayed (m r)
  have base : 1≤RG16.Lambda A (m r) := by change (1:ℝ)≤2+Real.log _; linarith [Real.log_nonneg Bx.le]
  have l : 1≤r/R.family.S.a (m r) := (one_le_pow₀ base).trans price.1
  refine ⟨?_,?_⟩
  · simpa only [one_mul] using (le_div_iff₀ a).mp l
  have upper' := price.2.trans (upper.trans (le_self_pow₀ Bx.le (by norm_num : (2:ℕ)≠0)))
  simpa only [mul_comm] using (div_le_iff₀ a).mp upper'

end YM.Integration.WilsonMatrixTicketLanesReportedWindow
