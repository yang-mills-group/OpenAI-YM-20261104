import YM.Integration.SelectedPlanPriorNumerator
import YM.Integration.ActualOriginalFieldCost
import YM.Integration.ActualInputGroundPrice
import YM.Integration.SelectedPlanKineticDenominator
import YM.Integration.FiniteCoefficientMass

/-! Polynomial control of the original selected Plan. The prior numerator,
ground coefficient, and kinetic denominator all use the same Run and model.
The finite induction changes neither the Plan nor its retained layer list. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedPlanCoefficientMass
open Function Filter Lattice Wilson RG Precision Exterior Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology ContDiff Classical BigOperators

private theorem mass_ge_one (c : ℕ → ℝ) (e : ℕ) :
    1 ≤ FiniteCoefficientMass.mass c e := by
  have h : 0 ≤ ∑ j ∈ Finset.range e, |c j| :=
    Finset.sum_nonneg (fun j _ => abs_nonneg (c j))
  unfold FiniteCoefficientMass.mass
  linarith

private theorem modifier_eq {G : Gauge} {C : Family G} {N period r : ℕ}
    (P : Plan C N period r) (m e : ℕ) (he : e ≤ r - 2) :
    SelectedPlanPriorNumerator.modifierCost P m e =
      SelectedPlanPriorJetBound.constant r *
        FiniteCoefficientMass.mass (P.coefficient m) e ^ (r + 4) := by
  have hs : (Finset.range (r - 2 + 1)).filter (fun j => j < e) = Finset.range e := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp only [SelectedPlanPriorNumerator.modifierCost, hs, FiniteCoefficientMass.mass]

/-- The complete same-list prior numerator has polynomial cost times a fixed
power of precisely the earlier coefficients. -/
theorem prior_polynomial {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule T.family J) (K : NumericPrices A) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ᶠ m : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = m →
      ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
        (M : AnalyticOutput caps Y K I) (e : ℕ), e ≤ J.order - 2 →
      ‖SelectedPlanGroundTriangle.priorCentered T M e
        (NativeNormalizedBondTest.actualField T hG datum.level datum.period)‖ ≤
        C * (A.admittedCost m)^d *
          FiniteCoefficientMass.mass (M.plan.coefficient datum.level) e ^ (J.order + 4) := by
  obtain ⟨C, hC, d, h⟩ := ActualOriginalFieldCost.uniform_cost
    (J.order + 4) caps.vacuumRank T hG hT A K
  let c := SelectedPlanPriorJetBound.constant J.order
  have hc : 0 < c := SelectedPlanPriorJetBound.constant_pos J.order
  let Cf : ℝ := (J.order + 5 : ℝ)^2 * (1 + c) * C
  have hCf : 0 < Cf := by dsimp only [Cf]; positivity
  refine ⟨Cf, hCf, d, ?_⟩
  filter_upwards [h] with m hm
  intro datum hlevel Y I M e he
  subst m
  let B := NativeNormalizedBondTest.actualField T hG datum.level datum.period
  let W := A.admittedCost datum.level
  let S := FiniteCoefficientMass.mass (M.plan.coefficient datum.level) e
  have hW : 0 ≤ W := A.admitted_cost_nonnegative datum.level
  have hS : 1 ≤ S := mass_ge_one (M.plan.coefficient datum.level) e
  have hSp : 1 ≤ S ^ (J.order + 4) := one_le_pow₀ hS
  have hF : 0 ≤ C * W^d := mul_nonneg hC.le (pow_nonneg hW d)
  have hn : e + 4 ≤ J.order + 4 := by omega
  have hp := SelectedPlanPriorNumerator.prior_bound T M.plan datum.level e (e + 4)
    M.vacuum datum.below.le (A.output_width_pos datum.level) hn B (C * W^d) hF
    (fun k hk => by
      simpa only [SelectedPlanPriorNumerator.field, B, W] using
        hm datum.cutoff datum.period datum.below.le M.vacuum k (hk.trans hn))
  change ‖SelectedPlanGroundTriangle.priorCentered T M e B‖ ≤ _ at hp
  have hmodifier : 1 + SelectedPlanPriorNumerator.modifierCost M.plan datum.level e ≤
      (1 + c) * S ^ (J.order + 4) := by
    rw [modifier_eq M.plan datum.level e he]
    change 1 + c * S ^ (J.order + 4) ≤ _
    nlinarith
  have hpower : ((e + 4 : ℕ) + 1 : ℝ)^2 ≤ (J.order + 5 : ℝ)^2 := by
    apply pow_le_pow_left₀ (by positivity)
    have hn' : e + 4 + 1 ≤ J.order + 5 := by omega
    exact_mod_cast hn'
  have hmul := mul_le_mul hpower hmodifier
    (by
      have hz := SelectedPlanPriorJetBound.constant_pos J.order
      rw [modifier_eq M.plan datum.level e he]
      positivity)
    (by positivity)
  have hfinal := mul_le_mul_of_nonneg_right hmul hF
  exact hp.trans (hfinal.trans_eq (by dsimp only [Cf]; ring))

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
        (M : AnalyticOutput caps Y K I) (_x : TestSpace J.tests) (e : ℕ),
      e ≤ J.order - 2 →
      |M.plan.coefficient datum.level e| ≤
        (C * (A.admittedCost m)^d) *
          FiniteCoefficientMass.mass (M.plan.coefficient datum.level) e ^ (J.order + 4) := by
  obtain ⟨Cp, hCp, dp, hp⟩ := prior_polynomial T hG hT (R := R) caps A K
  obtain ⟨Cg, hCg, dg, hg⟩ := ActualInputGroundPrice.ground_polynomial T hG hT (R := R) A
  let a : ℝ := 2 * (Fintype.card (TypeFace 2) : ℝ)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  let Cf : ℝ := 1 + a * (Cg + Cp)
  have hCf : 0 < Cf := by dsimp only [Cf]; positivity
  refine ⟨Cf, hCf, dg + dp + 1, ?_⟩
  filter_upwards [hp, hg, ActualCoarseStagePrice.coarse_cost T hG hT A]
    with m hp hg hstage
  intro datum hlevel Y I M x e he
  subst m
  let B := NativeNormalizedBondTest.actualField T hG datum.level datum.period
  let W := A.admittedCost datum.level
  let S := FiniteCoefficientMass.mass (M.plan.coefficient datum.level) e
  have hW1 : 1 ≤ W := A.admitted_cost_ge_one datum.level
  have hW : 0 ≤ W := zero_le_one.trans hW1
  have hS : 1 ≤ S := mass_ge_one (M.plan.coefficient datum.level) e
  have hSp : 1 ≤ S ^ (J.order + 4) := one_le_pow₀ hS
  have hSp0 : 0 ≤ S ^ (J.order + 4) := zero_le_one.trans hSp
  have hp' := hp datum rfl Y I M e he
  have hdegree : e + 2 ≤ J.order := by have h := J.order_ge_two; omega
  have hg' := hg datum rfl Y I x datum.tag (e + 2) (by omega) hdegree
  have hden := SelectedPlanKineticDenominator.coefficient_bound T hG hT
    hstage.1 M x e he
  dsimp only at hden hg'
  have hdp : W^dp ≤ W^(dg+dp) := pow_le_pow_right₀ hW1 (by omega)
  have hdg : W^dg ≤ W^(dg+dp) := pow_le_pow_right₀ hW1 (by omega)
  have hprior : ‖SelectedPlanGroundTriangle.priorCentered T M e B‖ ≤
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
  have hsum := add_le_add hground hprior
  have hdenom : 2 * ((Fintype.card (TypeFace 2) : ℝ) *
        Real.log (T.family.path.levels.clock.hatBeta (datum.level - 1))) ≤ a * W := by
    simpa only [a, mul_assoc] using mul_le_mul_of_nonneg_left hstage.2.2 ha
  have htotal := mul_le_mul hdenom hsum
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg ha hW)
  have hraw : |M.plan.coefficient datum.level e| ≤
      (a * (Cg + Cp)) * W^(dg+dp+1) * S^(J.order+4) := by
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
        (M : AnalyticOutput caps Y K I) (_x : TestSpace J.tests),
      1 + ∑ j ∈ Finset.range (J.order - 2 + 1), |M.plan.coefficient datum.level j| ≤
        C * (A.admittedCost m)^d := by
  obtain ⟨C, hC, d, h⟩ := coefficient_polynomial T hG hT (R := R) caps A K
  let E := FiniteCoefficientMass.degree (J.order + 4) (J.order - 2 + 1)
  refine ⟨(1 + C)^E, pow_pos (by linarith) _, d * E, ?_⟩
  filter_upwards [h] with m hm
  intro datum hlevel Y I M x
  have hc (j : ℕ) (hj : j < J.order - 2 + 1) :=
    hm datum hlevel Y I M x j (by omega)
  simpa only [FiniteCoefficientMass.mass, E] using
    FiniteCoefficientMass.polynomial_bound (J.order + 4) (J.order - 2 + 1) d C
      (by omega) hC.le (A.admittedCost m) (A.admitted_cost_ge_one m)
      (M.plan.coefficient datum.level) hc

end YM.Integration.SelectedPlanCoefficientMass
end
