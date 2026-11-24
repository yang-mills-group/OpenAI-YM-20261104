import YM.Integration.WilsonThermometerMarchEngineering
import YM.Integration.WilsonOriginalThermometerFineHarvest

/-! The original offset circuit clears all three actual parent collars on
every occupied compact shape cell, before taking the two regulator limits. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerMarchChambers
open Filter Set MeasureTheory Lattice Wilson RG Source Pressure Extraction PhysicalNext.Repeat.Legato
open WilsonSeparatedOriginalThermometerCells WilsonOriginalThermometerFineCover
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} (R : Run G)
local notation "β" => R.family.path.levels.clock.hatBeta

theorem original (simple : G.Simple) (φ : Test 3) (legal : tsupport φ ⊆ conf 3) :
    ∃ p₀ : ℕ, ∀ᶠ m : ℕ in atTop, ∀ p ≥ p₀, ∀ N (_ : m ≤ N) (r : ℝ),
      0 < r → r ≤ 1 → R.family.S.a m * (RG16.Lambda R.family.path.levels m)^5 ≤ r →
      ∀ z : Fin 3 → Site (R.family.side N p), weight φ (positions (R:=R) r (N,p)) z ≠ 0 →
        ∀ i i' : Fin 3, i ≠ i' → (R.family.path.levels.budget m).B^2 <
          separation (WilsonThermometerOwnOffsetJoint.origins R z m i)
            (WilsonThermometerOwnOffsetJoint.origins R z m i') := by
  obtain ⟨c,cp,score⟩ := WilsonOriginalThermometerFineCells.actual R φ legal
  obtain ⟨p₀,charts⟩ := eventually_atTop.mp score
  have grows := Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate R.family.path.levels simple)
  refine ⟨p₀,?_⟩
  filter_upwards [grows.eventually_ge_atTop (4/c)] with m large p hp N hm r pos cap room z live i i' off
  let x := Real.log (β m)
  let u := 2+x
  have xp : 0 ≤ x := Real.log_nonneg (R.family.path.levels.fits.delayed m).le
  have up : 1 ≤ u := by dsimp [u];linarith
  have Bb : (((R.family.path.levels.budget m).B:ℕ):ℝ) ≤ u^2 := by
    change (⌈x^2⌉₊:ℝ) ≤ (2+x)^2
    nlinarith only [Nat.ceil_lt_add_one (sq_nonneg x),xp]
  have Bsq := pow_le_pow_left₀ (Nat.cast_nonneg (R.family.path.levels.budget m).B) Bb 2
  have B4 : (((R.family.path.levels.budget m).B:ℕ):ℝ)^2+3 ≤ 4*u^4 := by
    nlinarith only [Bsq,(one_le_pow₀ up : 1≤u^4)]
  have height : 4 ≤ u*c := by
    have rate := (div_le_iff₀ cp).mp large
    change 4 ≤ x*c at rate
    dsimp only [u];nlinarith only [rate,cp]
  have guard : 4*u^4 ≤ u^5*c := by
    calc 4*u^4 ≤ (u*c)*u^4 := mul_le_mul_of_nonneg_right height (by positivity)
         _ = _ := by ring
  have at_m := mul_le_mul_of_nonneg_left (B4.trans guard) (R.family.S.a_pos m).le
  have paid := mul_le_mul_of_nonneg_right room cp.le
  change R.family.S.a m*u^5*c ≤ r*c at paid
  have top := R.family.S.strictAnti.antitone hm
  have charged : R.family.S.a m * (((R.family.path.levels.budget m).B^2+1:ℕ):ℝ) + 2*R.family.S.a N ≤ r*c := by
    push_cast
    nlinarith only [at_m,paid,top]
  have hits := charts p hp N m hm r pos cap z live i i' off ((R.family.path.levels.budget m).B^2+1) charged
  simpa only [WilsonThermometerOwnOffsetJoint.origins,WilsonThermometerOwnOffsetNectar.location,
    dif_pos hm,WilsonThermometerOwnOffsetTale.site] using (Nat.lt_of_succ_le hits)

end YM.Integration.WilsonThermometerMarchChambers
