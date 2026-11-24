import YM.Integration.WilsonOriginalNectarInvoice
import YM.Integration.WilsonThermometerOwnOffsetInvoice
import YM.Integration.WilsonThermometerOffsetLedger

/-! The actual displaced source's full original regular and forced budget,
at every upper age, fits the already elected reporting radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNectarRadius
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetSource WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetTale WilsonThermometerOwnOffsetNectar
open WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetInvoice
open Push.Local WilsonThermometerOffsetResidue
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G)
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "B" => WilsonThermometerOffsetLedger.cash R

theorem salary (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (d:ℕ) :
    ∀ᶠ j:ℕ in atTop, 1 ≤ β j ∧ 1 ≤ B d j ∧ B d j ≤ β j := by
  filter_upwards [WilsonThermometerOffsetLedger.original R simple shop d,
    (WardBin.bell R.alloy.B.a simple).eventually_ge_atTop 4] with j booked warm
  have warm' : (4:ℝ) ≤ β j := warm
  have high : (1:ℝ) ≤ β j := by linarith
  have half : 0 < β j/2 := by linarith
  have lg : Real.log (β j) ≤ β j / 2 := by
    have first:=Real.log_le_sub_one_of_pos half
    have two:=Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
    rw [Real.log_div (by linarith) (by norm_num)] at first
    linarith
  refine ⟨high,booked.2.1,booked.2.2.trans ?_⟩
  change 1+Real.log (2+Real.log (β j)) ≤ β j
  have tail:=Real.log_le_sub_one_of_pos (show 0 < 2+Real.log (β j) by linarith [Real.log_nonneg high])
  linarith

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (d t:ℕ)
    (positive:1 ≤ t) :
    ∀ᶠ k:ℕ in atTop, ∀ {j N p:ℕ} (_:k ≤ j) (hn:j ≤ N)
      (z:Site (R.family.side N p)) {V:Sight R.family d p} {r:Emblems R.family d}
      (_:Enrolled R.makes R.doors B k N p d (digits R N p z) V r)
      (y:Palette R.family d) (_:size y ≤ 1),
      let P:=R.family.path.rep N p j
      let o:=site R hn z
      ∃Q:Coefficient (R.family.labels.level d) (R.family.side j p),
        Q.Format o R.family.params P ∧
        Q.remBound o P (kappa R.family.path j) (radius R t k j)⁻¹ ∧
        invoice Q o (R.family.localSection d) P=state (k:=k) R V r y z j := by
  obtain ⟨k₀,late⟩:=eventually_atTop.mp (salary R simple shop d)
  filter_upwards [eventually_ge_atTop k₀,WilsonThermometerOwnOffsetRadii.paid R simple (d+1) t]
    with k early fiscal j N p hj hn z V r H y bounded
  obtain ⟨Q,form,cap,same⟩:=WilsonOriginalNectarInvoice.original R z H hj hn y
  refine ⟨Q,form,rem_mono cap ?_,same⟩
  have hB:=late j (early.trans hj)
  have X:=ascent R H y bounded hj hn
  have bpow:β j ≤ β j^t :=by
    simpa only [pow_one] using (pow_le_pow_right₀ hB.1 positive)
  have cost:B d j*size (finer r hj y) ≤ β j^t*span R k j :=
    mul_le_mul (hB.2.2.trans bpow) X (by unfold size;positivity) (pow_nonneg (hB.1.trans' zero_le_one) _)
  rw [factor_size]
  have base:=span_pos R k j
  have rwpos:=radius_pos R t k j hj
  rw [inv_eq_one_div,le_div_iff₀ rwpos,mul_comm _ (radius R t k j)]
  calc
    _ ≤ radius R t k j*((span R k j)^d*(β j^t*span R k j)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left cost (pow_nonneg base.le _)) rwpos.le
    _ = radius R t k j*(span R k j)^(d+1)*β j^t := by rw [pow_succ];ring
    _ ≤ 1 := fiscal j hj

end YM.Integration.WilsonOriginalNectarRadius
end
