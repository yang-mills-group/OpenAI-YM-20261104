import YM.Integration.WilsonMovingMentorBentPrice

/-! Refund the actual bent regular-action bill into the coupling of every measured original cutoff and period at that date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingMentorBentTemperature
open LocalTaylorR2
open Exponent
open King (overD capping SupplyF)
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Ovens Time UVNext UVNext.CouplingReset Daisy.Charity.RG12 Tail
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open CalendarStep
open Reel Recoil Capstone Strand Rain Roost Mallow PhysicalNext.Repeat.Legato UVExtension Spire Orchard Mast Oasis LocalTaylorR2.Marker
open MergeProof Marker Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF
open ConnectedActivityE6

theorem purchased {G : Gauge} (R : Run G) (simple : G.Simple) (q : ℕ)
    {δ : ℝ} (positive : 0 < δ) :
    ∀ᶠ start : ℕ in atTop, ∀ m ≥ start, ∀ N per, m ≤ N → ∀ p ≥ q+2, ∀ η : ℝ, η ≤ 1 →
      Reel.upfront (R.alloy.B.a.clock.hatBeta m) p η ≤
        δ * (Coat.gStep (R.family.path.rep N per m).beta)^q := by
  let A := R.alloy.B.a
  have rise : Tendsto A.clock.hatBeta atTop atTop :=
    tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  obtain ⟨t,ht⟩ := eventually_atTop.mp (rise.eventually_ge_atTop (2*(2:ℝ)^q/δ))
  refine eventually_atTop.mpr ⟨t,fun start from_t m late N per cut p order η hη => ?_⟩
  let x := A.clock.hatBeta m
  let β := (R.family.path.rep N per m).beta
  have one : 1 ≤ x := (A.fits.delayed m).le
  have hx : 0 < x := zero_lt_one.trans_le one
  have band : β ∈ Shoot.band A m := ((R.T.sticks N per).prices m (Nat.zero_le _) cut).2
  have hb : 0 < β := (half_pos hx).trans_le band.1
  have multiplier : 2*(2:ℝ)^q / x ≤ δ := by
    apply (div_le_iff₀ hx).2
    simpa only [mul_comm δ x] using (div_le_iff₀ positive).mp (ht m (from_t.trans late))
  have rate : (requested (p+1) η) ≤ -(q:ℝ)/2 + (-1) := by
    have width : (q:ℝ)+2 ≤ (p:ℝ) := by exact_mod_cast order
    unfold requested
    push_cast
    linarith only [width,hη]
  have words : x^(-(q:ℝ)/2) = ((Real.sqrt x)⁻¹)^q := by
    rw [Real.sqrt_eq_rpow,inv_pow,← Real.rpow_natCast,← Real.rpow_mul hx.le,← Real.rpow_neg hx.le]
    congr 1
    ring
  have refund : (Real.sqrt x)⁻¹ ≤ 2*Coat.gStep β := by
    change (Real.sqrt x)⁻¹ ≤ 2*(Real.sqrt β)⁻¹
    rw [←one_div,←div_eq_mul_inv,div_le_div_iff₀ (Real.sqrt_pos.2 hx) (Real.sqrt_pos.2 hb),one_mul]
    have upper : Real.sqrt β ≤ Real.sqrt (2*x) := Real.sqrt_le_sqrt band.2
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (2:ℝ))] at upper
    exact upper.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
      (Real.sqrt_nonneg x))
  have gp : 0 ≤ Coat.gStep β := inv_nonneg.2 (Real.sqrt_nonneg _)
  change 2*x^requested (p+1) η ≤ δ*(Coat.gStep β)^q
  calc
    2*x^requested (p+1) η ≤ 2*x^(-(q:ℝ)/2 + (-1)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one rate) (by norm_num)
    _ = (2/x)*((Real.sqrt x)⁻¹)^q := by
      rw [Real.rpow_add hx,Real.rpow_neg_one,words,div_eq_mul_inv]; ring
    _ ≤ (2/x)*(2*Coat.gStep β)^q := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) refund q) (by positivity)
    _ = (2*(2:ℝ)^q/x)*(Coat.gStep β)^q := by rw [mul_pow]; ring
    _ ≤ δ*(Coat.gStep β)^q := mul_le_mul_of_nonneg_right multiplier (pow_nonneg gp q)

end YM.Integration.WilsonMovingMentorBentTemperature
end
