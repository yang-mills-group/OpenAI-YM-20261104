import YM.Integration.WilsonLimitConstruction.FundedCoverKineticMeasurement

/-! The measured finite-to-cover coefficient with its held-root receipt controls all finite coefficients on the
true Plan using the same original admitted schedule before every period. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonLimitConstruction.FundedCoverCoefficientMass
open Function Filter Lattice Wilson RG Precision Exterior Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Comparison.RG02.Assembly
open FundedCoverKineticMeasurement
open scoped Topology ContDiff Classical BigOperators

/-- The original selected coefficient satisfies a genuine triangular recurrence.
All income comes from the original action and layer receipts. -/
theorem coefficient_polynomial {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule T.family J) (K : NumericPrices A) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ᶠ m : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = m →
      ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
        (M : FundedPhysicalCatalogue.Purchase caps K I) (x : TestSpace J.tests) (e : ℕ),
      e ≤ J.order - 2 → Tested T Y I M hG x →
      |M.plan.coefficient datum.level e| ≤
        (C * (A.admittedCost m)^d) *
          FiniteCoefficientMass.mass (M.plan.coefficient datum.level) e ^ (J.order + 4) := by
  obtain ⟨Cp, hCp, dp, hp⟩ := FundedCoefficientPrior.polynomial T hG hT (R := R) caps A K
  obtain ⟨Cg, hCg, dg, hg⟩ := ActualInputGroundPrice.ground_polynomial T hG hT (R := R) A
  let a : ℝ := 2 * (Fintype.card (TypeFace 2) : ℝ)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  let Cf : ℝ := 1 + a * (Cg + Cp + 1)
  have hCf : 0 < Cf := by dsimp only [Cf]; positivity
  refine ⟨Cf, hCf, dg + dp + 1, ?_⟩
  filter_upwards [hp, hg, ActualCoarseStagePrice.coarse_cost T hG hT A]
    with m hp hg hstage
  intro datum hlevel Y I M x e he contacted
  subst m
  let B := NativeNormalizedBondTest.actualField T hG datum.level datum.period
  let W := A.admittedCost datum.level
  let S := FiniteCoefficientMass.mass (M.plan.coefficient datum.level) e
  have hW1 : 1 ≤ W := A.admitted_cost_ge_one datum.level
  have hW : 0 ≤ W := zero_le_one.trans hW1
  have hS : 1 ≤ S := FundedCoefficientPrior.mass_ge_one (M.plan.coefficient datum.level) e
  have hSp : 1 ≤ S ^ (J.order + 4) := one_le_pow₀ hS
  have hSp0 : 0 ≤ S ^ (J.order + 4) := zero_le_one.trans hSp
  have hp' := hp datum rfl M.plan M.vacuum e he
  have hdegree : e + 2 ≤ J.order := by have h := J.order_ge_two; omega
  have hg' := hg datum rfl Y I x datum.tag (e + 2) (by omega) hdegree
  have hden := FundedCoverKineticMeasurement.bound T Y I M hG hT x e he hstage.1
  dsimp only at hden hg'
  have hdp : W^dp ≤ W^(dg+dp) := pow_le_pow_right₀ hW1 (by omega)
  have hdg : W^dg ≤ W^(dg+dp) := pow_le_pow_right₀ hW1 (by omega)
  have hprior : ‖FundedCoefficientPrior.centered T M.plan datum.level e B‖ ≤
      Cp * W^(dg+dp) * S^(J.order+4) :=
    hp'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdp hCp.le) hSp0)
  have hground :
      ‖Symmetry.Orbit.ground (datum.kernel Y)
          (RG08.Line.green (T.family.path.levels.clock.op datum.level datum.period))
          datum.tag (I.colors x) J.order (e + 2) B -
        Symmetry.Orbit.ground (datum.kernel Y)
          (RG08.Line.green (T.family.path.levels.clock.op datum.level datum.period))
          datum.tag (I.colors x) J.order (e + 2) 0‖ ≤
      Cg * W^(dg+dp) * S^(J.order+4) := by
    apply hg'.trans
    calc
      Cg * W^dg ≤ Cg * W^(dg+dp) := mul_le_mul_of_nonneg_left hdg hCg.le
      _ ≤ _ := le_mul_of_one_le_right
        (mul_nonneg hCg.le (pow_nonneg hW _)) hSp
  have hcut : ‖difference T Y I M x e B‖ ≤ (1:ℝ)*W^(dg+dp)*S^(J.order+4) := by
    apply (contacted e he).trans
    rw [one_mul]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hW1) hSp
  have hsum := add_le_add (add_le_add hground hprior) hcut
  have hdenom : 2 * ((Fintype.card (TypeFace 2) : ℝ) *
        Real.log (T.family.path.levels.clock.hatBeta (datum.level - 1))) ≤ a * W := by
    simpa only [a, mul_assoc] using mul_le_mul_of_nonneg_left hstage.2.2 ha
  have htotal := mul_le_mul hdenom hsum
    (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)) (mul_nonneg ha hW)
  have hraw : |M.plan.coefficient datum.level e| ≤
      (a * (Cg + Cp + 1)) * W^(dg+dp+1) * S^(J.order+4) := by
    apply hden.trans
    exact htotal.trans_eq (by simp only [pow_add, pow_one]; ring)
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by dsimp only [Cf]; linarith)
      (pow_nonneg hW _)) hSp0)

/-- A single polynomial controls the complete finite coefficient mass of the
same Plan, uniformly before the cutoff, period, selected output and tests. -/
theorem mass_polynomial {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule T.family J) (K : NumericPrices A) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ᶠ m : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = m →
      ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
        (M : FundedPhysicalCatalogue.Purchase caps K I) (x : TestSpace J.tests),
      Tested T Y I M hG x →
      1 + ∑ j ∈ Finset.range (J.order - 2 + 1), |M.plan.coefficient datum.level j| ≤
        C * (A.admittedCost m)^d := by
  obtain ⟨C, hC, d, h⟩ := coefficient_polynomial T hG hT (R := R) caps A K
  let E := FiniteCoefficientMass.degree (J.order + 4) (J.order - 2 + 1)
  refine ⟨(1 + C)^E, pow_pos (by linarith) _, d * E, ?_⟩
  filter_upwards [h] with m hm
  intro datum hlevel Y I M x contacted
  have hc (j : ℕ) (hj : j < J.order - 2 + 1) :=
    hm datum hlevel Y I M x j (by omega) contacted
  simpa only [FiniteCoefficientMass.mass, E] using
    FiniteCoefficientMass.polynomial_bound (J.order + 4) (J.order - 2 + 1) d C
      (by omega) hC.le (A.admittedCost m) (A.admitted_cost_ge_one m)
      (M.plan.coefficient datum.level) hc

end YM.Integration.WilsonLimitConstruction.FundedCoverCoefficientMass
end
