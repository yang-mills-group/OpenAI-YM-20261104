import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Net
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.One



set_option warningAsError false

/-!
# Terminal density for the one-slot reflection estimate

`Books` requires an active `Bands` representation at the stop, with a
per-mark support radius and an absolute budget. The represented signal
pushes the old product from level `N` to `k`, inserts the new observable
there, then pushes the combined density to `l` using the same unnormalized
vacuum. The coarse observable enters at its own level.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.RMirror.Stop
open Set Filter Function MeasureTheory RG Wilson Lattice Cells Block Extraction Org
open Marker Overlay Tower Net
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} (C : Family G) {k l m p N : ℕ}

abbrev Port (p m : ℕ) := Stock.census (Flags C.path p m)

/-- Per-mark bounds for the combined terminal signal at the fixed stop. -/
structure Books (N p : ℕ) (v : C.book.Token) (hl : m ≤ l) (hk : l ≤ k) (hn : k ≤ N)
    (A : Qry C.path p k) (u r d b w : ℝ) : Prop where
  current : ∃ B : Bands (Port C p m) (C.path.rep N p l), B.Active ∧
    (∀ i, B.origins i = (C.S.toDepth hl p).embed i) ∧
    B.Radial (fun _ => w) u r d b ∧
    ∀ s : (Port C p m).Mode, ∀ U,
      (B.density U).part s = encoded C.path v.1 (hl.trans hk) hn hk (source C v N p) A s.val U


















end YM.ProjectorNext.RMirror.Stop
