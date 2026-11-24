import YM.SignedWilsonExpansion.Public.World
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedElectedMatrixRetainedContinuumLimitPupil

set_option autoImplicit false
noncomputable section

universe u
namespace IssuedBridge.PostedElectedMatrixRetainedContinuumLimitVision
open YM YM.Integration YM.Answer.ContinuumLimit
open Climb Lattice Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction
open Election SignedWilsonExpansion.Museum
open scoped Classical Topology

variable {G : Gauge} {simple : G.Simple} {ε : ℝ} {e : Axis} {O : OrderS G}

/-- The chosen construction supplies the paid run. Its retained pupil publishes
the matrix, trace and actual field desk on the same refinement. -/
theorem original (E : Construction.{u} simple ε e O)
    (cohort : Ultrafilter (ℕ × ℕ) → Prop)
    (issued : ∀ (f : Extraction.Order) (l : Ultrafilter (ℕ × ℕ)),
      (l : Filter (ℕ × ℕ)) ≤ f.fuse → cohort l)
    (f : Extraction.Order) :
    ∃ V : Vision E f,
      (V.pupil.Y : Filter (ℕ × ℕ)) ≤ (f.refine V.g).fuse ∧ cohort V.pupil.Y ∧
      Log.MatrixTicket (C := E.paths.family) V.pupil.S V.pupil.last.sector.derivatives
        (V.pupil.Y : Filter (ℕ × ℕ)) ∧
      SingleLog V.pupil.last V.pupil.P.port ∧ LogTrace V.pupil.last V.pupil.P.port ∧
      Trace.Target.Result.{u} V.pupil.last simple ∧ Trace.Target.Exclusion.{u} V.pupil.last ∧
      V.colours = standT V.pupil.S V.pupil.last.room.kernel.laws V.pupil.last.room.kernel.spin := by
  obtain ⟨M, w, X, uses, first, lies, chosen, matrix, single, trace, result, exclude⟩ :=
    PostedElectedMatrixRetainedContinuumLimitPupil.original.{u} E.paths simple E.receipts.paid cohort issued f
  let V : Vision E f :=
    ⟨M, w, uses, X, first, standT M.S M.last.room.kernel.laws M.last.room.kernel.spin⟩
  exact ⟨V, lies, chosen, matrix, single, trace, result, exclude, rfl⟩

end IssuedBridge.PostedElectedMatrixRetainedContinuumLimitVision
