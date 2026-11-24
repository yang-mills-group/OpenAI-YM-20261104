import YM.Integration.ActualOriginalQInitialInput
import YM.Integration.ActualOriginalFeeGrowth
import YM.Integration.WilsonStartupClock
import YM.Integration.WilsonReportHarvestUpperRange

/-! Growth of the actual initial MS source normalization on the logarithmic
upper interval of a genuine measured trajectory. The register order is fixed
before both regulators and every independent root. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldScale
open Function Filter Finset Lattice Wilson RG Marker Precision Source
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open MergeProof MergeProof.Accent ActualOriginalQCharges ActualOriginalQPackets ActualOriginalQReaders
open OPE.Therm RG05Readout RG05Readout.Native RG05Readout.Flatten
open scoped Topology BigOperators Classical
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {B : MS.Local.Physical.Deck G}
    (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B) (J : Request V) (A : NumericSchedule R.family J)
local notation "base" => ActualOriginalQPointSetup.pointDatum R J 0 0 (fun _ => 0)

omit [DecidableEq V] [Fintype V] in
private theorem reader (p b : ℕ) (o : V → Site (R.family.side b p)) (i : V) :
    readerPrice (ActualOriginalQPointSetup.pointDatum R J p b o) i = readerPrice (base) i := by
  simp only [readerPrice, ActualOriginalQPointSetup.pointDatum, ActualOriginalQPointDatum.constant_eq]
  simp only [ActualOriginalQPointDatum.datum, originR, ratio_one]

private theorem capped (d : LocalFormal.Datum R.family (Stock.census V)) (Q : MS.Land.Prescription B)
    (o : V → Site (R.family.side (d.level+1) d.period)) (μ : ℝ) (orders : V → ℕ) {P : ℝ} (pos : 1 ≤ P)
    (charges : ∀s : Slot u, ‖fee Q u (μ-R.family.S.scale d.cutoff) orders s‖ ≤ P) :
    ActualOriginalQInitialInput.normalizer R hG u J A d Q o μ orders ≤
      P * max 1 (totalRowPrice (base) u (fun _ => 1) 1) := by
  let point := ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
  let width := (ActualOriginalQInitialInput.schedule R hG u J A).inputWidth d.level
  let w := fun _ : V => (1 : ℝ)
  have wp : ∀i,0<w i := fun _ => zero_lt_one
  have small : width ≤ 1 := min_le_right _ _
  have pay (s : Row (R:=R) u) : rowPrice point u w width s ≤ rowPrice (base) u w 1 s := by
    have mass : 0 ≤ rowMass (base) u s := by
      simpa only [rowPrice,w,Poly.toll,Finset.prod_const_one,one_mul,zero_mul,Real.exp_zero,mul_one]
        using row_price_nonneg (base) u w 0 wp s
    have same : rowMass point u s = rowMass (base) u s := by
      unfold rowMass
      rw [reader R J]
    unfold rowPrice
    rw [same]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right small (Nat.cast_nonneg _)))
      (mul_nonneg (Poly.worth wp _).le mass)
  change max 1 (∑s : Row (R:=R) u, ‖fee Q u (μ-R.family.S.scale d.cutoff) orders s.1‖ * rowPrice point u w width s) ≤ _
  refine max_le ?_ ?_
  · exact one_le_mul_of_one_le_of_one_le pos (le_max_left _ _)
  · calc
      _ ≤ ∑s : Row (R:=R) u, P * rowPrice (base) u w 1 s := Finset.sum_le_sum fun s _ =>
          mul_le_mul (charges s.1) (pay s) (row_price_nonneg point u w width wp s) (zero_le_one.trans pos)
      _ = P * totalRowPrice (base) u w 1 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (zero_le_one.trans pos)

include hG in
/-- The reported upper portion may contain arbitrarily many nonbare steps.
The Wilson clock buys the *last* block of the actual cutoff as well. -/
theorem clock : ∃ C : ℝ, 0 < C ∧ ∀ᶠ j : ℕ in atTop, ∀ {m t : ℕ}, j ≤ t →
    WilsonReportHarvestUpperRange.eligible R.family.S m j t →
    1+‖R.family.S.scale (t+1)‖ ≤ C*R.family.path.levels.clock.hatBeta j := by
  obtain ⟨a, ap, bill⟩ := WilsonStartupClock.growth R hG
  obtain ⟨j₀, late⟩ := eventually_atTop.1 bill
  refine ⟨2*a,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop j₀] with j begun
  intro m t jt geometry
  let L := R.family.path.levels
  have cap : L.clock.hatBeta t ≤ 2*L.clock.hatBeta j := by
    have pos := (L.fits.delayed m).le
    change R.family.S.scale t-R.family.S.scale m ≤ 2*(R.family.S.scale j-R.family.S.scale m) at geometry
    have mul := mul_le_mul_of_nonneg_left geometry (Gauge.slopeConstant_pos hG).le
    unfold Calendar.hatBeta at pos ⊢
    dsimp only [L] at *
    linarith
  calc
    _ ≤ a*L.clock.hatBeta t := late _ (begun.trans jt)
    _ ≤ a*(2*L.clock.hatBeta j) := mul_le_mul_of_nonneg_left cap ap.le
    _ = _ := by ring

/-- The exponent and constant precede the reporting date, the original cutoff
and period, every position, and every retained prescription row up to `K`. -/
theorem original (Q : MS.Land.Prescription B) (μ : ℝ) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ e : ℕ, ∀ᶠ j : ℕ in atTop, ∀ {m t : ℕ}, j ≤ t →
      WilsonReportHarvestUpperRange.eligible R.family.S m j t →
      ∀ (d : LocalFormal.Datum R.family (Stock.census V)), d.cutoff = t+1 →
      ∀ (o : V → Site (R.family.side (d.level+1) d.period)) (orders : V → ℕ), (∀i,orders i ≤ K) →
      ActualOriginalQInitialInput.normalizer R hG u J A d Q o μ orders ≤ C*(R.family.path.levels.clock.hatBeta j)^e := by
  obtain ⟨c, cp, e, fees⟩ := ActualOriginalFeeGrowth.shifted_bound B Q u K μ
  obtain ⟨a, ap, dates⟩ := clock R hG
  let W := max 1 (totalRowPrice (base) u (fun _ => 1) 1)
  let D := max 1 c * (max 1 a)^e
  have wp : 1 ≤ W := le_max_left _ _
  have dp : 1 ≤ D := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ (le_max_left _ _))
  refine ⟨D*W,mul_pos (zero_lt_one.trans_le dp) (zero_lt_one.trans_le wp),e,?_⟩
  filter_upwards [dates] with j price
  intro m t jt eligible d cut o orders upper
  let β := R.family.path.levels.clock.hatBeta j
  have bp : 1 ≤ β := (R.family.path.levels.fits.delayed _).le
  have P : 1 ≤ D*β^e := one_le_mul_of_one_le_of_one_le dp (one_le_pow₀ bp)
  have hold : 1+‖R.family.S.scale d.cutoff‖ ≤ (max 1 a)*β := by
    rw [cut]
    exact (price jt eligible).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans bp))
  have charges (s : Slot u) : ‖fee Q u (μ-R.family.S.scale d.cutoff) orders s‖ ≤ D*β^e := by
    calc
      _ ≤ c*(1+‖R.family.S.scale d.cutoff‖)^e := fees s.1 (orders s.1) (upper s.1) s.2 _
      _ ≤ max 1 c*((max 1 a)*β)^e := mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ (by positivity) hold e)
        (by positivity) (zero_le_one.trans (le_max_left _ _))
      _ = _ := by unfold D; rw [mul_pow];ring
  exact (capped R hG u J A d Q o μ orders P charges).trans_eq (by dsimp only [W]; ring)

end YM.Integration.WilsonReportingPrescribedOldScale
