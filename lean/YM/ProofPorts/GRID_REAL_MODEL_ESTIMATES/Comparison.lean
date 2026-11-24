import YM.Next.UV_STRESS.Influence
import YM.Next.UV_STRESS.Rates
import YM.Push.GRID_APPROXIMATION.Iterate



/-!
# Grid-stop and coarse reflection variables

The comparison uses one Wilson family and the full grid of link cells.
The old reflected factors are fixed when conditioning on the fine
configuration. The new factors enter the same conditional expectation.
Disjoint dependency cones allow the product calculation while accounting
for shared tags. The resulting identity transfers a supplied physical
attenuation estimate to the reflection variables on that grid.
-/

set_option autoImplicit false
noncomputable section

namespace YM.ProofPorts.GridRealModelEstimates

open RG Lattice Wilson Cells Filter MeasureTheory
open Push.GridApprox Next.UVStress
open scoped Topology BigOperators

lemma region_eq_window (n : Side) (r : ℕ) : region n r = window (0 : Site n) r := by
  simp [region, window]

variable {G : Gauge} (C : Family G)
variable {k m h N p r : ℕ}















lemma origin_local {U : Config G (C.side k p) → ℂ} (t : h ≤ k) (hk : k ≤ N)
    (hU : Interior (region (C.side k p) r) U) :
    Interior (window 0 (Push.GridApprox.grows C.path.levels k r hk)) (backTo C.path N p hk U) := by
  rw [region_eq_window] at hU
  rw [← show anchor C.S p (t.trans hk) 0 = 0 from (C.S.toDepth (t.trans hk) p).root.map_zero]
  apply backTo_local C.path N p t hk 0 r
  rw [show anchor C.S p t 0 = 0 from (C.S.toDepth t p).root.map_zero]
  exact hU

lemma origin_fits (p : ℕ) (t : h ≤ k) (hk : k ≤ N) (hroom : room C.path.levels h k r) :
    window 0 (Push.GridApprox.grows C.path.levels k r hk) ⊆ (tilesAt C.S p (t.trans hk)).chamber 0 := by
  have he := room_fits p C.path.levels r t hk hroom 0
  rw [show anchor C.S p (t.trans hk) 0 = 0 from (C.S.toDepth (t.trans hk) p).root.map_zero] at he
  exact he

variable {C}



end YM.ProofPorts.GridRealModelEstimates
