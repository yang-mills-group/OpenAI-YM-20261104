import YM.Integration.WilsonLimitConstruction.FundedCoverCoefficientMass
import YM.Integration.SelectedPlanPredictedStripe

/-! One physical native tail pays the complete signed predictor and its two
actual fine/coarse coupling ratios before all periods and marked outputs. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonLimitConstruction.FundedCoverPredictionRatio
open Function Filter Lattice Wilson RG Precision Exterior Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Comparison.RG02.Assembly
open MatchingLedger.Compass.Income Pert.Asymptotics
open FundedCoverKineticMeasurement
open scoped Topology ContDiff Classical BigOperators

private theorem polynomial_le_mass {G : Gauge} {C : Family G} {N period r : ℕ}
    (P : Plan C N period r) (m : ℕ) {g : ℝ} (hg : 0 ≤ g) (hg1 : g ≤ 1) :
    |P.poly m g| ≤ FiniteCoefficientMass.mass (P.coefficient m) (r - 2 + 1) := by
  have hterm (j : ℕ) : ‖P.coefficient m j * g^j‖ ≤ |P.coefficient m j| := by
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hg]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hg hg1)
  have hsum := (norm_sum_le (Finset.range (r - 2 + 1))
    (fun j => P.coefficient m j * g^j)).trans
    (Finset.sum_le_sum (fun j _ => hterm j))
  exact (show |P.poly m g| ≤ ∑ j ∈ Finset.range (r - 2 + 1),
      |P.coefficient m j| by simpa only [Plan.poly, Real.norm_eq_abs] using hsum).trans
    (le_add_of_nonneg_left zero_le_one)

/-- The complete selected polynomial is small relative to the actual fine
inverse-square coupling, on one tail before any output is selected. -/
theorem polynomial_small {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule T.family J) (K : NumericPrices A)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = m →
      ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
        (M : FundedPhysicalCatalogue.Purchase caps K I),
      Tested T Y I M hG (fun v => (0 : (J.tests v).Mood)) →
      |M.plan.poly datum.level
          (regulatorRun T.family datum.cutoff datum.period (datum.level + 1))| *
        regulatorRun T.family datum.cutoff datum.period (datum.level + 1)^2 ≤ epsilon := by
  obtain ⟨C, hC, d, hm⟩ := FundedCoverCoefficientMass.mass_polynomial
    T hG hT (R := R) caps A K
  have hgSmall := (tendsto_add_atTop_nat 1).eventually
    (Currency.g_small hG T.makes 1 zero_lt_one)
  filter_upwards [hm, ActualNumericCouplingSmallness.eventually_cost_coupling_small
    T hG A C hC.le d epsilon hepsilon, hgSmall] with m hm hc hgSmall
  intro datum hlevel Y I M contact
  subst m
  let g := regulatorRun T.family datum.cutoff datum.period (datum.level + 1)
  have hg : 0 < g := Weather.runs_pos T.family T.makes
    (Nat.succ_le_of_lt datum.below) datum.period
  have hg1 : g ≤ 1 := (hgSmall datum.cutoff datum.period
    (Nat.succ_le_of_lt datum.below)).le
  have hmass := hm datum rfl Y I M (fun v => (0 : (J.tests v).Mood)) contact
  have hp := (polynomial_le_mass M.plan datum.level hg.le hg1).trans hmass
  exact (mul_le_mul_of_nonneg_right hp (sq_nonneg g)).trans
    (hc datum.cutoff datum.period datum.below)

/-- The very same predictor is positive and its gain is comparable with the
actual fine coupling. The original two inverse couplings keep their own values. -/
theorem predicted_fine {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule T.family J) (K : NumericPrices A) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = m →
      ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
        (M : FundedPhysicalCatalogue.Purchase caps K I),
      Tested T Y I M hG (fun v => (0 : (J.tests v).Mood)) →
      0 < M.plan.predict datum.level ∧
      (1 / 2 : ℝ) ≤ Currency.gain (M.plan.predict datum.level) /
          regulatorRun T.family datum.cutoff datum.period (datum.level + 1) ∧
      Currency.gain (M.plan.predict datum.level) /
          regulatorRun T.family datum.cutoff datum.period (datum.level + 1) ≤ 2 := by
  filter_upwards [polynomial_small T hG hT (R := R) caps A K (1/2) (by norm_num)]
    with m hm
  intro datum hlevel Y I M contact
  subst m
  let g := regulatorRun T.family datum.cutoff datum.period (datum.level + 1)
  let beta := T.family.path.β datum.cutoff datum.period (datum.level + 1)
  let b := M.plan.predict datum.level
  let p := M.plan.poly datum.level g
  have hg : 0 < g := Weather.runs_pos T.family T.makes
    (Nat.succ_le_of_lt datum.below) datum.period
  have hbeta : 0 < beta := Weather.iceborn T.family T.makes
    (Nat.succ_le_of_lt datum.below) datum.period
  have hepoch : beta * g^2 = 1 := Weather.epoch T.family T.makes
    (Nat.succ_le_of_lt datum.below) datum.period
  have heq : b = beta + p := by
    dsimp only [b, beta, p, g]
    rw [Plan.predict, if_neg (Nat.ne_of_lt datum.below)]
  have hsmall : |p| * g^2 ≤ (1/2 : ℝ) := hm datum rfl Y I M contact
  have hpg : |p * g^2| ≤ (1/2 : ℝ) := by
    simpa only [abs_mul, abs_of_nonneg (sq_nonneg g)] using hsmall
  have hp := abs_le.mp hpg
  have hbprod : b * g^2 = 1 + p * g^2 := by rw [heq, add_mul, hepoch]
  have hg2 : 0 < g^2 := pow_pos hg 2
  have hband : b ∈ Currency.stripe beta := by
    constructor
    · apply (mul_le_mul_iff_left₀ hg2).mp
      calc
        (beta / 4) * g^2 = (beta * g^2) / 4 := by ring
        _ = 1/4 := by rw [hepoch]
        _ ≤ b * g^2 := by linarith
    · apply (mul_le_mul_iff_left₀ hg2).mp
      calc
        b * g^2 ≤ 3/2 := by linarith
        _ ≤ (4 * beta) * g^2 := by rw [mul_assoc, hepoch]; norm_num
  have hgain := Currency.sizes_band hbeta hband
  have hGainBeta : Currency.gain beta = g := rfl
  rw [hGainBeta] at hgain
  refine ⟨Currency.stripe_pos hbeta hband, ?_, ?_⟩
  · exact (le_div_iff₀ hg).2 (by linarith [hgain.1])
  · exact (div_le_iff₀ hg).2 hgain.2

/-- The selected rendered vacuum uses a gain ratio between one quarter and
four relative to the original actual coarse regulator, uniformly in all data. -/
theorem actual_ratio {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule T.family J) (K : NumericPrices A) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = m →
      ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
        (M : FundedPhysicalCatalogue.Purchase caps K I),
      Tested T Y I M hG (fun v => (0 : (J.tests v).Mood)) →
      0 < M.plan.predict datum.level ∧
      (1 / 4 : ℝ) ≤ Currency.gain (M.plan.predict datum.level) /
          regulatorRun T.family datum.cutoff datum.period datum.level ∧
      Currency.gain (M.plan.predict datum.level) /
          regulatorRun T.family datum.cutoff datum.period datum.level ≤ 4 := by
  filter_upwards [predicted_fine T hG hT (R := R) caps A K,
    ActualRunAdjacentCoupling.eventually_ratio T hG] with m hm ha
  intro datum hlevel Y I M contact
  subst m
  have hp := hm datum rfl Y I M contact
  have ha := ha datum.cutoff datum.period datum.below
  let gf := regulatorRun T.family datum.cutoff datum.period (datum.level + 1)
  let gc := regulatorRun T.family datum.cutoff datum.period datum.level
  have hf : 0 < gf := Weather.runs_pos T.family T.makes
    (Nat.succ_le_of_lt datum.below) datum.period
  have hc : 0 < gc := Weather.runs_pos T.family T.makes datum.below.le datum.period
  have hfactor : Currency.gain (M.plan.predict datum.level) / gc =
      (Currency.gain (M.plan.predict datum.level) / gf) * (gf / gc) := by
    field_simp [hf.ne', hc.ne']
  have hlo := mul_le_mul hp.2.1 ha.1 (by norm_num : (0:ℝ) ≤ 1/2)
    (le_trans (by norm_num : (0:ℝ) ≤ 1/2) hp.2.1)
  have hhi := mul_le_mul hp.2.2 ha.2
    (le_trans (by norm_num : (0:ℝ) ≤ 1/2) ha.1) (by norm_num : (0:ℝ) ≤ 2)
  refine ⟨hp.1, ?_, ?_⟩
  · rw [hfactor]
    exact (show (1/4 : ℝ) ≤ (1/2 : ℝ) * (1/2 : ℝ) by norm_num).trans hlo
  · rw [hfactor]
    exact hhi.trans (by norm_num : (2 : ℝ) * 2 ≤ 4)

private theorem stripe_of_small {a beta p g : ℝ} (ha : 0 < a) (hg : 0 < g)
    (hepoch : beta * g^2 = 1) (hlo : a / 2 ≤ beta) (hhi : beta ≤ 3 * a)
    (hsmall : |p| * g^2 ≤ (1/4 : ℝ)) : beta + p ∈ Currency.stripe a := by
  have hp : |p| ≤ beta / 4 := by
    apply (mul_le_mul_iff_left₀ (pow_pos hg 2)).mp
    calc
      |p| * g^2 ≤ 1/4 := hsmall
      _ = (beta / 4) * g^2 := by
        calc
          (1/4 : ℝ) = (beta * g^2) / 4 := by rw [hepoch]
          _ = (beta / 4) * g^2 := by ring
  have hp' := abs_le.mp hp
  constructor <;> linarith

/-- The original selected Plan satisfies precisely the beta-range conclusion
of Room.predicted, uniformly before the cutoff, period and output choices. -/
theorem stripe {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule T.family J) (K : NumericPrices A) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = m →
      ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
        (M : FundedPhysicalCatalogue.Purchase caps K I),
      Tested T Y I M hG (fun v => (0 : (J.tests v).Mood)) →
      M.plan.predict datum.level ∈
        Currency.stripe (Currency.B T.family.path.levels datum.level) := by
  filter_upwards [polynomial_small T hG hT
    (R := R) caps A K (1/4) (by norm_num),
    ActualRunAdjacentHatBeta.three_halves T hG] with m hm ht
  intro datum hlevel Y I M contact
  subst m
  let g := regulatorRun T.family datum.cutoff datum.period (datum.level + 1)
  let beta := T.family.path.β datum.cutoff datum.period (datum.level + 1)
  let a := Currency.B T.family.path.levels datum.level
  have ha : 0 < a := WardBin.hot T.family.path.levels datum.level
  have hg : 0 < g := Weather.runs_pos T.family T.makes
    (Nat.succ_le_of_lt datum.below) datum.period
  have hepoch : beta * g^2 = 1 := Weather.epoch T.family T.makes
    (Nat.succ_le_of_lt datum.below) datum.period
  have hband := (T.makes.wilson.represents datum.cutoff datum.period
    (datum.level + 1) (Nat.succ_le_of_lt datum.below)).band
  have hmono := WilsonStartup.Timing.hat_mono T.family.path.levels (G.slopeConstant_pos hG).le
    (Nat.le_succ datum.level)
  have hnext : T.family.path.levels.clock.hatBeta (datum.level + 1) ≤
      (3/2 : ℝ) * a := ht
  have hlo : a / 2 ≤ beta := by
    exact (div_le_div_of_nonneg_right hmono (by norm_num)).trans hband.1
  have hhi : beta ≤ 3 * a := by
    have hcap : beta ≤ 2 * T.family.path.levels.clock.hatBeta (datum.level + 1) := hband.2
    linarith only [hcap, hnext]
  have hs := stripe_of_small ha hg hepoch hlo hhi (hm datum rfl Y I M contact)
  simpa only [Plan.predict, if_neg (Nat.ne_of_lt datum.below)] using hs

end YM.Integration.WilsonLimitConstruction.FundedCoverPredictionRatio
end
