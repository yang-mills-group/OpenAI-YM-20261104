import YM.Integration.ActualWilsonForcedRow

/-! A forced-only coefficient on the selected residual's native carrier,
with all partners, their inherited support and the physical divided bill. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.Integration.ActualWilsonResidualCoefficient

open Lattice Wilson RG Marker Source Labels RG3.Script.Picnic RG3.Forms
open RG3.Law LocalComparison Finset Extra.Histories Relay Bid
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained LocalComparison.Global Comparison.RG02
open ActualWilsonForcedRow
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {P : Rep G n} {V : Type} [DecidableEq V]
    {R : Census V} {d : ℕ}

/-- The complete native solution on the original forced slots of this deck. -/
def shell (F : Frame G d) (v : V) (D : Deck R P) : Coefficient F n :=
  { primary (D.contents.origins v) (0 : F.Coeff) with forced := solution v D }

/-- Gauge invariance, support and eligibility are supplied by the active deck. -/
theorem shell_format (F : Frame G d) (v : V) (D : Deck R P)
    (h : D.Active) (A : Hol G) : (shell F v D).Format (D.contents.origins v) A P := by
  have h0 : (primary (D.contents.origins v) (0 : F.Coeff)).Format
      (D.contents.origins v) A P := primary_format _
  have he i := Emerald.access v D h i
  exact ⟨h0.smooth, h0.origin, h0.identity_null, h0.projects, fun i => (he i).2.2.2.1,
    fun i => (he i).2.2.2.2, fun i => (he i).2.1, fun i => (he i).2.2.1, fun i => (he i).1⟩

section Selected

variable [Fintype V] {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C R} {caps : Handoff.OutputCapacities}
    {Y : Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta}
    {M : AnalyticOutput caps Y K F} {delta : ℝ} {forcedOrder : ℕ}

/-- The physical, unnormalized row has a full source coefficient at its
native divided price on the retained coarse representation. -/
theorem selected (S : Chosen K I M) (H : Bounds S delta forcedOrder) (v : V)
    (hreserve : (C.path.levels.budget datum.level).supportExponent ≤ J.outputSupport)
    (x : IndependentTests J.tests) :
    let g := Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level+1)
    let D := S.output.residual.leaf (testInclusion J.tests x)
    ∃ q : Coefficient (C.labels.level (J.outputWeight v)) (C.side datum.level datum.period),
      q.x = 0 ∧ q.regular = 0 ∧ q.forced = solution v D ∧
      q.Format (F.coarseRoots v) C.params S.output.carrier.rep ∧
      q.remBound (F.coarseRoots v) S.output.carrier.rep (forcedDivisor C datum.level)
        (F.kernelCosts v * g^forcedOrder / F.outputRadii v) := by
  intro g D
  let T := pullback (testInclusion J.tests) S.output.residual
  let cost : R.Mode → ℝ := envelopeProduct F.kernelCosts
  let D' := (priceNormalized cost T).leaf x
  let α := F.kernelCosts v
  have hα : cost (R.fire v) = α := by simp [cost,α,envelopeProduct,Census.fire]
  let q := Extra.Histories.stretch (α : ℂ) (shell (C.labels.level (J.outputWeight v)) v D')
  have hactive : D'.Active := H.residual_price.budget.active x
  have hroot : D'.contents.origins v = F.coarseRoots v :=
    congrFun (priceNormalized cost T).root v
  have hformat : q.Format (F.coarseRoots v) C.params S.output.carrier.rep := by
    rw [← hroot]
    exact stretch_format _ (shell_format _ _ _ hactive _)
  have hr : q.regular = 0 := by
    ext i U
    simp [q,shell,Extra.Histories.stretch,primary]
  have hf : q.forced = solution v D := by
    funext i U
    have hh := solution_scaled (T := T) cost v (H.residual_price.positive _) x i U
    rw [hα, solution_pullback] at hh
    exact hh.symm
  obtain ⟨t,ht,hs⟩ := native_price S H v hreserve
  have hb : SumBudget (fun i => S.output.carrier.rep.p.mass
      (S.output.carrier.rep.activities.forced i).support (t i))
      (forcedDivisor C datum.level * (α * g^forcedOrder / F.outputRadii v)) := by
    rw [S.output.carrier.point]
    convert hs using 1
    dsimp only [α,g]
    ring
  refine ⟨q, by simp [q,shell,Extra.Histories.stretch,primary], hr, hf, hformat, 0,
    α*g^forcedOrder/F.outputRadii v, le_rfl,
    nonneg_of_mul_nonneg_right (Push.AbsoluteSums.budget_nonneg hb)
      H.residual_price.budget.divisor, (zero_add _).le, H.residual_price.budget.divisor,
    ⟨fun _ => 0, budget0 _ _, fun i => ?_⟩, t, hb, fun i => ⟨(ht i).1, fun U => ?_⟩⟩
  · rw [hr]
    exact (regular0 S.output.carrier.rep.p _ (F.coarseRoots v)).2
  rw [hf]
  exact (ht i).2 x U

end Selected
end YM.Integration.ActualWilsonResidualCoefficient
