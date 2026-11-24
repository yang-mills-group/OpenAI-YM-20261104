import YM.Integration.ActualRunShortHulls
import YM.Integration.ActualNumericShortHulls

/-! The actual numerical schedule supplies one geometric admission threshold
before all marked data and physical periods. Both original tori are retained.
This is a composition of the numerical size estimate and finite-box injectivity;
it adds no short-hull, field, or period hypothesis. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunShortHullsTail

open Filter Lattice Wilson RG Marker LocalComparison
open FullQLocal FullQLocal.RenderedStep

/-- A single stage admits every marked datum on the original Run's two tori.
The threshold is chosen before the census, datum, and its physical period. -/
theorem atRun {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    (R : PhysicalNext.Repeat.Legato.Run G) (hG : G.Simple)
    {J : Request V} (A : NumericSchedule R.family J) (K : NumericPrices A) :
    ∃ first : ℕ, ∀ (marks : Census V) (datum : LocalFormal.Datum R.family marks),
      first ≤ datum.level → Numeric.Retained.ShortHulls K datum := by
  obtain ⟨first, hfirst⟩ := Filter.eventually_atTop.1
    (ActualNumericShortHulls.atRun R hG A K)
  refine ⟨first, ?_⟩
  intro marks datum hdatum
  exact ActualRunShortHulls.of_size K datum
    (hfirst datum.level hdatum datum.period).1
    (hfirst datum.level hdatum datum.period).2

end YM.Integration.ActualRunShortHullsTail
end
