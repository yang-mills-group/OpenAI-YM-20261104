import YM.Integration.FullQLocalRetainedGrant

/-! Concrete finite-box admission for the actual numerical qlocal interface.
The numerical side inequalities remain explicit here; the actual-Run growth
supplier is composed separately. No short-hull premise is silently discarded. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunShortHulls

open Lattice Wilson RG Marker LocalComparison
open FullQLocal FullQLocal.RenderedStep

/-- Translation does not change injectivity of a cover box strictly smaller
than half the original torus side. -/
theorem translated_box_injective (n : Side) (r : ℕ)
    (hsize : 2 * r < n.val) (o : Site n) :
    Set.InjOn (fun z : Cover => o + wrap n z) (↑(box r) : Set Cover) := by
  have hsize' : (2 : ℤ) * r < n.val := by exact_mod_cast hsize
  have centered (z : Cover) (hz : z ∈ box r) :
      ∀ i, -(n.val : ℤ) < 2 * z i ∧ 2 * z i ≤ n.val := by
    obtain ⟨hl, hu⟩ := box_test.mp hz
    intro i
    have hlo := hl i
    have hup := hu i
    omega
  intro x hx y hy hxy
  exact wrap_injOn n (centered x hx) (centered y hy) (add_left_cancel hxy)

/-- Both original tori, every translated root and the selected numerical
price multiplier are retained in the actual Numeric.ShortHulls receipt. -/
theorem of_size {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {marks : Census V} {C : Family G} {J : Request V}
    {A : NumericSchedule C J} (K : NumericPrices A)
    (datum : LocalFormal.Datum C marks)
    (coarse : 2 * (K.hullMultiplier datum.level *
      (1 + C.path.levels.clock.coverSize datum.level)) <
        (C.side datum.level datum.period).val)
    (fine : 2 * (K.hullMultiplier datum.level *
      (1 + C.path.levels.clock.coverSize (datum.level + 1))) <
        (C.side (datum.level + 1) datum.period).val) :
    Numeric.Retained.ShortHulls K datum where
  coarse o := translated_box_injective _ _ coarse o
  fine o := translated_box_injective _ _ fine o

end YM.Integration.ActualRunShortHulls
end
