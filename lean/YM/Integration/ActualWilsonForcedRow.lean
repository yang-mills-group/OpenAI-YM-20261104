import YM.Integration.ActualWilsonGraphReclosure
import YM.RG3.Law.Retrieve

/-! The common support-weighted price of the native singleton forced row in a
physical local comparison, with the complete test normalization retained. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.Integration.ActualWilsonForcedRow

open Filter Lattice Wilson RG Marker Source Labels RG3.Script.Picnic
open RG3.Law LocalComparison Finset Extra.Histories
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {P : Rep G n} {V : Type} [DecidableEq V]
  {R : Census V} {X : Type*} {o : V → Site n} {T : Taste X o P R}
  {p : BudgetPoint} {w : V → ℝ} {κ r b : ℝ}

/-- The one common numerical majorant controls all tests, fields and original
forced partners in the prescribed output norm. -/
theorem common (H : FullBudget p T w κ r b) (v : V) :
    ∃ t : ℕ → ℝ, (∀ i, 0 ≤ t i ∧ ∀ x U, ‖solution v (T.leaf x) i U‖ ≤ t i) ∧
      SumBudget (fun i => p.mass (P.activities.forced i).support (t i)) (κ*b/(w v)) := by
  let fee (ij : ℕ × ℕ) := if T.menu.marks ij.1 ij.2 = R.fire v then H.black ij else 0
  let loc (i : ℕ) := (P.activities.forced i).support
  have hn (i : ℕ × ℕ) : 0 ≤ fee i := by
    unfold fee
    split
    · exact H.black_nonnegative i
    exact le_rfl
  have hsum : SumBudget (fun ij : ℕ × ℕ => p.mass (loc ij.1) (fee ij)) (κ*b/(w v)) := by
    rw [div_eq_inv_mul]
    refine Push.AbsoluteSums.budget_mono (Push.AbsoluteSums.budget_scale (x := (w v)⁻¹) (inv_nonneg.2 (H.radii v).le)
      (H.forcedTotal v)) (fun ij => (hn _).trans (p.loMass _ _ (hn _))) ?_
    intro ij
    unfold fee loc
    split
    next he =>
      rw [he, if_pos (show v ∈ (R.fire v).val from mem_singleton_self _),
        Poly.solo_toll, ← mul_assoc, inv_mul_cancel₀ (H.radii v).ne', one_mul]
    unfold BudgetPoint.mass
    rw [mul_zero]
    exact mul_nonneg (inv_nonneg.2 (H.radii v).le) ((H.forcedTotal v).1 ij)
  let t (i : ℕ) := ∑' j : ℕ, fee (i,j)
  have hfee := hsum.2.1.of_nonneg_of_le hn (fun ij => p.loMass _ _ (hn ij))
  have htest (i : ℕ) (x : X) (U : Config G n) : ‖solution v (T.leaf x) i U‖ ≤ t i := by
    let a (j : ℕ) := if T.menu.marks i j = R.fire v then T.menu.force x i j U else 0
    have ha (j : ℕ) : ‖a j‖ ≤ fee (i,j) := by
      unfold a fee
      dsimp only
      split
      · exact H.forced x i j U
      simp
    have hs := hfee.comp_injective (Prod.mk_right_injective i)
    have ht := hs.of_nonneg_of_le (fun j => norm_nonneg _) ha
    exact (norm_tsum_le_tsum_norm ht).trans (ht.tsum_le_tsum ha hs)
  have hs : SumBudget (fun i => ∑' j : ℕ, p.mass (loc i) (fee (i,j))) (κ*b/(w v)) :=
    ⟨fun i => tsum_nonneg (fun j => hsum.1 (i,j)),
      ((summable_prod_of_nonneg hsum.1).mp hsum.2.1).2, hsum.2.1.tsum_prod ▸ hsum.2.2⟩
  refine ⟨t, fun i => ⟨tsum_nonneg (fun j : ℕ => hn (i,j)), htest i⟩, ?_⟩
  simpa only [BudgetPoint.mass, t, tsum_mul_left, loc] using hs

/-- The singleton coefficient of an absolutely summed marked row. -/
theorem each_solution [Fintype V] (D : RG3.Forms.Deck R P) (v : V) (i : ℕ) (U : Config G n)
    (h : Summable (fun j => D.contents.tagged i j U)) :
    (D.contents.each i U).part (R.fire v) = solution v D i U := by
  simp only [Overlay.Bands.each, Poly.part_plus, Poly.part_send, if_neg (R.fire_hot v),
    zero_add, Poly.share h]
  unfold solution
  apply tsum_congr
  intro j
  simp only [Overlay.Bands.tagged, Poly.part_send, eq_comm (a := R.fire v)]

/-- Restricting the test family leaves every forced amplitude unchanged. -/
theorem solution_pullback {Y : Type*} (f : Y → X) (v : V) (y : Y) (i : ℕ)
    (U : Config G n) : solution v ((pullback f T).leaf y) i U =
      solution v (T.leaf (f y)) i U := rfl

theorem solution_scaled (cost : R.Mode → ℝ) (v : V) (hα : 0 < cost (R.fire v))
    (x : X) (i : ℕ) (U : Config G n) :
    solution v (T.leaf x) i U = ((cost (R.fire v) : ℝ) : ℂ) *
      solution v ((priceNormalized cost T).leaf x) i U := by
  let α := cost (R.fire v)
  change (∑' j : ℕ, if T.menu.marks i j = R.fire v then T.menu.force x i j U else 0) =
    (α : ℂ) * (∑' j : ℕ, if T.menu.marks i j = R.fire v then
      (cost (T.menu.marks i j))⁻¹ • T.menu.force x i j U else 0)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  by_cases hj : T.menu.marks i j = R.fire v
  · rw [if_pos hj, if_pos hj, hj, Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
      mul_inv_cancel₀ (by exact_mod_cast hα.ne' : (α : ℂ) ≠ 0), one_mul]
  rw [if_neg hj, if_neg hj, mul_zero]


/-- Multiplying back the genuine singleton price restores the original row
chosen before the field and every independent test. -/
theorem physical {cost : R.Mode → ℝ} (H : RelativeBudget p T w κ cost r b) (v : V) :
    ∃ t : ℕ → ℝ, (∀ i, 0 ≤ t i ∧ ∀ x U, ‖solution v (T.leaf x) i U‖ ≤ t i) ∧
      SumBudget (fun i => p.mass (P.activities.forced i).support (t i))
        (cost (R.fire v) * (κ*b/(w v))) := by
  let α := cost (R.fire v)
  have hα : 0 < α := H.positive _
  obtain ⟨t, ht, hsum⟩ := common H.budget v
  refine ⟨fun i => α*t i, fun i => ⟨mul_nonneg hα.le (ht i).1, fun x U => ?_⟩, ?_⟩
  · rw [solution_scaled cost v hα, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
    exact mul_le_mul_of_nonneg_left ((ht i).2 x U) hα.le
  have hh := Push.AbsoluteSums.budget_scale (x := α) hα.le hsum
  convert hh using 2 with i
  unfold BudgetPoint.mass
  ring


section Selected

variable [Fintype V]

open Comparison.RG02 FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained LocalComparison.Global

variable {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C R} {caps : Handoff.OutputCapacities}
    {Y : Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta}
    {M : AnalyticOutput caps Y K F} {delta : ℝ} {forcedOrder : ℕ}

/-- The chosen physical residual has a single support bill for every test.
All retained addresses and the fine cutoff coupling are the original ones. -/
theorem retained (S : Chosen K I M) (H : Bounds S delta forcedOrder) (v : V) :
    ∃ t : ℕ → ℝ, (∀ i, 0 ≤ t i ∧ ∀ (x : IndependentTests J.tests) U,
      ‖solution v (S.output.residual.leaf (testInclusion J.tests x)) i U‖ ≤ t i) ∧
      SumBudget (fun i => (A.outputNorm datum.level).mass
        (S.output.carrier.rep.activities.forced i).support (t i))
        (F.kernelCosts v * (forcedDivisor C datum.level *
          (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level+1))^forcedOrder /
          F.outputRadii v)) := by
  simpa only [solution_pullback, envelopeProduct, Census.fire, Finset.prod_singleton] using
    physical H.residual_price v

/-- The original Wilson support currency pays the same individual bound if
the purchased output support exponent covers the level's original exponent. -/
theorem native_price (S : Chosen K I M) (H : Bounds S delta forcedOrder) (v : V)
    (hreserve : (C.path.levels.budget datum.level).supportExponent ≤ J.outputSupport) :
    ∃ t : ℕ → ℝ, (∀ i, 0 ≤ t i ∧ ∀ (x : IndependentTests J.tests) U,
      ‖solution v (S.output.residual.leaf (testInclusion J.tests x)) i U‖ ≤ t i) ∧
      SumBudget (fun i => (C.path.levels.budget datum.level).mass
        (S.output.carrier.rep.activities.forced i).support (t i))
        (F.kernelCosts v * (forcedDivisor C datum.level *
          (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level+1))^forcedOrder /
          F.outputRadii v)) := by
  obtain ⟨t,ht,hs⟩ := retained S H v
  refine ⟨t,ht,Push.AbsoluteSums.budget_mono hs (fun i =>
    ((ht i).1.trans ((C.path.levels.budget datum.level).loMass _ _ (ht i).1))) ?_⟩
  intro i
  unfold BudgetPoint.mass
  rw [(A.output_norm datum.level).block, (A.output_norm datum.level).reserve]
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hreserve (Nat.cast_nonneg _))) (ht i).1

end Selected

end YM.Integration.ActualWilsonForcedRow
