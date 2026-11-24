import YM.Integration.ZeroAwareVacuumPackets
import YM.Extra.ITERATION_NO_LOSS.TermNorm

/-!
# Regularity on every original vacuum row

The canonical atom supplies regularity on its true footprint. Nonzero rows
use the retained containment proof, while coefficient-zero rows use their
literal zero function on the unchanged original support. No row is removed.

The numerical bound still uses its actual canonical atom estimate. Flatness,
affine Hessian nullity, row permutations, and the summed derivative price
needed by Payload.Invoice are separate obligations.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison.Global

open Lattice Wilson RG
open IterationFour.Vacuum

variable {G : Gauge} {n : Side} {layers : List (Piece G n)}
    {p : BudgetPoint} {rankCap : ℕ} {width budget : ℝ}

/-- Original-support regularity follows from the retained atom, even on zero rows. -/
theorem ZeroAwareVacuumPackets.regular
    (H : ZeroAwareVacuumPackets layers p rankCap width budget)
    (a : Piece G n) (ha : a ∈ layers) (i : ℕ) :
    p.Regular (a.packet.labels i).support (a.packet.action i) := by
  have hrow : a.packet.action i =
      fun U => (H.atom a i).unmasked U (a.packet.labels i).site :=
    funext (H.original_action a ha i)
  rw [hrow]
  by_cases hz : (H.atom a i).magnitude = 0
  · have hzero : (fun U => (H.atom a i).unmasked U (a.packet.labels i).site) =
        (fun _ : Config G n => 0) :=
      funext (fun U => YM.Integration.FullQLocal.ZeroRows.unmasked_zero
        (H.atom a i) hz (a.packet.labels i).site U)
    rw [hzero]
    exact AnalyticBridge.VerifiedReset.reg_const 0
  exact AnalyticBridge.VerifiedReset.reg_larger
    (Extra.Iteration.Derivs.canonical_regular (H.atom a i)
      (a.packet.labels i).site p (H.invariant a ha i))
    (H.support a ha i hz)

/-- The only remaining termwise numerical premise is the canonical atom bound. -/
theorem ZeroAwareVacuumPackets.canonical_bound
    (H : ZeroAwareVacuumPackets layers p rankCap width budget)
    (a : Piece G n) (ha : a ∈ layers) (i : ℕ) (c : ℝ)
    (hbound : p.supBounds (a.packet.labels i).site
      ((H.atom a i).footprint (a.packet.labels i).site)
      (fun U => (H.atom a i).unmasked U (a.packet.labels i).site) c) :
    p.supBounds (a.packet.labels i).site (a.packet.labels i).support
      (a.packet.action i) c :=
  (H.regular_bounds a ha i c
    (Extra.Iteration.Derivs.canonical_regular (H.atom a i)
      (a.packet.labels i).site p (H.invariant a ha i)) hbound).2

end YM.Integration.LocalComparison.Global

end
