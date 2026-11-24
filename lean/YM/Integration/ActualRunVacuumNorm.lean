import YM.Integration.LocalComparisonGlobalContract
import YM.FullVolume.Cross

/-!
The fixed requested norm preserves the physical density when its threshold is
unchanged. Native kinetic rigidity accepts that norm: its numerical Quotes
are eventually supplied by the same original Run. This does not manufacture
an affine-null regular family or a paid reset from an unclosed qlocal output.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunVacuumNorm

open Filter Lattice Wilson RG
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Currency
open YM.Integration.LocalComparison YM.Integration.LocalComparison.Global
open scoped Topology BigOperators

variable {G : Gauge}

/-- Norm orders and support tariffs do not change this full physical density. -/
theorem eval_same_threshold {n : Side} (Q : Rep G n) (p q : BudgetPoint)
    (h : p.threshold = q.threshold) :
    ({Q with p := p} : Rep G n).eval = ({Q with p := q} : Rep G n).eval := by
  funext U
  simp only [Rep.eval, Rep.exponent, PathData.inChannels, PathData.principal,
    PathData.baseTerm, PathData.kept, PathData.atomSeries, Atom.placed, Activities.additive,
    Activities.regularOccurrence, Activities.gas, Activities.gasOccurrence,
    Activities.admissible, h]

/-- Native wave-test Quotes hold at the fixed requested output norm on the
same trajectory, before all cutoffs and periods. -/
theorem output_quotes (R : Run G) (hG : G.Simple) {V : Type}
    [DecidableEq V] [Fintype V] (J : Setup V) (A : Admission R.family J) :
    ∀ᶠ i : ℕ in atTop,
      Pert.Kinetic.Quotes (A.outputNorm i)
        (R.family.path.levels.params i).width
        (R.family.path.levels.params i).paths
        (R.family.path.levels.clock.loopCap i)
        (R.family.path.levels.clock.allowance i)
        (Kinetic.price R.family i) := by
  filter_upwards [Kinetic.quote_eventually R.family hG,
    (Next.Rank.Station.hat_rate R.family.path.levels hG).eventually_ge_atTop
      J.outputSupport⁻¹] with i hq hs
  refine ⟨hq.pos, hq.jump, hq.width, hq.paths, hq.loop, hq.price, hq.price_lo,
    ?_, ?_, ?_⟩
  · simpa only [(A.output_norm i).block] using hq.cover
  · rw [(A.output_norm i).reserve]
    have hb : R.family.path.levels.clock.hatBeta i ≤
        2 * R.family.path.levels.clock.hatBeta i := by
      have hp := WardBin.hot R.family.path.levels i
      linarith
    exact hs.trans (hb.trans (Kinetic.two_hat_le R.family i))
  · simpa only [(A.output_norm i).threshold] using hq.inv_field

end YM.Integration.ActualRunVacuumNorm
end
