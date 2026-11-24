import YM.Integration.SelectedPlanPriorNumerator
import YM.Integration.ActualOriginalFieldCost
import YM.Integration.FiniteCoefficientMass

/-! The finite lower-order physical numerator is priced on any genuine paid
Plan, before all cutoffs, periods and future signed analytic selections. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonLimitConstruction.FundedCoefficientPrior
open Function Filter Lattice Wilson RG Precision Exterior Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology ContDiff Classical BigOperators

def centered {G : Gauge} (R : Run G) {N period r : ℕ}
    (P : Plan R.family N period r) (m e : ℕ)
    (B : fieldDir G (R.family.side m period) 1) : ℂ :=
  jet (SelectedPlanClearedNumerator.numerator R (SelectedPlanTriangular.prior P e) m)
      (e+4) (1,B) -
    jet (SelectedPlanClearedNumerator.numerator R (SelectedPlanTriangular.prior P e) m)
      (e+4) (1,0)

theorem mass_ge_one (c : ℕ → ℝ) (e : ℕ) :
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
theorem polynomial {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule T.family J) (K : NumericPrices A) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ᶠ m : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = m →
      ∀ (P : Plan T.family datum.cutoff datum.period J.order),
      GradedVacuumLayers (P.layers datum.level) (A.outputNorm datum.level)
        J.order caps.vacuumRank (A.outputWidth datum.level) (K.geometry datum.level) →
      ∀ e : ℕ, e ≤ J.order - 2 →
      ‖centered T P datum.level e
        (NativeNormalizedBondTest.actualField T hG datum.level datum.period)‖ ≤
        C * (A.admittedCost m)^d *
          FiniteCoefficientMass.mass (P.coefficient datum.level) e ^ (J.order + 4) := by
  obtain ⟨C, hC, d, h⟩ := ActualOriginalFieldCost.uniform_cost
    (J.order + 4) caps.vacuumRank T hG hT A K
  let c := SelectedPlanPriorJetBound.constant J.order
  have hc : 0 < c := SelectedPlanPriorJetBound.constant_pos J.order
  let Cf : ℝ := (J.order + 5 : ℝ)^2 * (1 + c) * C
  have hCf : 0 < Cf := by dsimp only [Cf]; positivity
  refine ⟨Cf, hCf, d, ?_⟩
  filter_upwards [h] with m hm
  intro datum hlevel P paid e he
  subst m
  let B := NativeNormalizedBondTest.actualField T hG datum.level datum.period
  let W := A.admittedCost datum.level
  let S := FiniteCoefficientMass.mass (P.coefficient datum.level) e
  have hW : 0 ≤ W := A.admitted_cost_nonnegative datum.level
  have hS : 1 ≤ S := mass_ge_one (P.coefficient datum.level) e
  have hSp : 1 ≤ S ^ (J.order + 4) := one_le_pow₀ hS
  have hF : 0 ≤ C * W^d := mul_nonneg hC.le (pow_nonneg hW d)
  have hn : e + 4 ≤ J.order + 4 := by omega
  have hp := SelectedPlanPriorNumerator.prior_bound T P datum.level e (e + 4)
    paid datum.below.le (A.output_width_pos datum.level) hn B (C * W^d) hF
    (fun k hk => by
      simpa only [SelectedPlanPriorNumerator.field, B, W] using
        hm datum.cutoff datum.period datum.below.le paid k (hk.trans hn))
  change ‖centered T P datum.level e B‖ ≤ _ at hp
  have hmodifier : 1 + SelectedPlanPriorNumerator.modifierCost P datum.level e ≤
      (1 + c) * S ^ (J.order + 4) := by
    rw [modifier_eq P datum.level e he]
    change 1 + c * S ^ (J.order + 4) ≤ _
    nlinarith
  have hpower : ((e + 4 : ℕ) + 1 : ℝ)^2 ≤ (J.order + 5 : ℝ)^2 := by
    apply pow_le_pow_left₀ (by positivity)
    have hn' : e + 4 + 1 ≤ J.order + 5 := by omega
    exact_mod_cast hn'
  have hmul := mul_le_mul hpower hmodifier
    (by
      have hz := SelectedPlanPriorJetBound.constant_pos J.order
      rw [modifier_eq P datum.level e he]
      positivity)
    (by positivity)
  have hfinal := mul_le_mul_of_nonneg_right hmul hF
  exact hp.trans (hfinal.trans_eq (by dsimp only [Cf]; ring))

end YM.Integration.WilsonLimitConstruction.FundedCoefficientPrior
end
