import YM.Integration.SelectedPlanPredictionRatio
import YM.Integration.ActualRunAdjacentHatBeta
import YM.Extra.WILSON_STARTUP.Fast

/-! The same selected predictor lies in the literal hatted-beta stripe used
by the native Room.predicted field. The source is the derived full polynomial
mass, the actual fine beta band and the original clock increment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedPlanPredictedStripe
open Function Filter Lattice Wilson RG Precision Exterior Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Comparison.RG02.Assembly
open MatchingLedger.Compass.Income Pert.Asymptotics
open scoped Topology ContDiff Classical BigOperators

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
theorem predicted {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule T.family J) (K : NumericPrices A) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = m →
      ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
        (M : AnalyticOutput caps Y K I),
      M.plan.predict datum.level ∈
        Currency.stripe (Currency.B T.family.path.levels datum.level) := by
  filter_upwards [SelectedPlanPredictionRatio.polynomial_small T hG hT
    (R := R) caps A K (1/4) (by norm_num),
    ActualRunAdjacentHatBeta.three_halves T hG] with m hm ht
  intro datum hlevel Y I M
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
  have hs := stripe_of_small ha hg hepoch hlo hhi (hm datum rfl Y I M)
  simpa only [Plan.predict, if_neg (Nat.ne_of_lt datum.below)] using hs

end YM.Integration.SelectedPlanPredictedStripe
end
