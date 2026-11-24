import YM.MergeProof.Glacier
import YM.MergeProof.South.Window

/-!
Exact original physical marked source and top-level integrability suppliers,
separated from the later propagation and representation estimates.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PhysicalJoin.Marked
open Function Filter Finset MeasureTheory Lattice Wilson RG Marker Extra.Histories
open MergeProof MergeProof.Accent Extra.Trajectories
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{I:Type} [Fintype I] [DecidableEq I]{N p k:ℕ}
local notation "P"=> C.path.levels
local notation "ρ"=> C.path.rep N p
local notation "μ" k:max=> prior G (C.side k p)
variable (d:I→ℕ)(s:(i:I)→ C.label (d i)) (o:(j:ℕ)→I→Site (C.side j p)) (z:I→Motion)
abbrev sourceItem (N:ℕ)(i:I) := MergeProof.item C (d i) N p (s i) (fun j=>o j i) (z i)
abbrev topJoint (Γ:Census I) (N:ℕ) := Accent.birth Γ (C.path.rep N p N) (sourceItem d s o z N)
abbrev pushedJoint (Γ:Census I) (N:ℕ)(j:ℕ)(hj:j≤N) := gust C.path N p N (topJoint d s o z Γ N) j hj
variable (hC:C.Makes){S:Table C.book}{f:Extraction.Order}
variable {w:I→ℝ}
include hC
lemma topLive (Γ:Census I) (N:ℕ) : Integrable (topJoint d s o z Γ N) (μ N):=by
   apply (hatCont C N p (sourceItem d s o z N) (fun i=> generics C N p (d i) o (fun _=>s i) z i)
     (show Continuous ((C.path.rep N p N).eval) from by rw [(hC.wilson.starts ..).2]; exact bare_cont _) Γ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
end YM.PhysicalJoin.Marked
