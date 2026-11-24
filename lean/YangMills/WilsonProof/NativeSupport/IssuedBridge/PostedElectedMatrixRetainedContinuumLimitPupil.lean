import YM.SignedWilsonExpansion.Warehouse.Wish
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedMatrixRetainedContinuumLimitOrder

set_option autoImplicit false
noncomputable section

universe u
namespace IssuedBridge.PostedElectedMatrixRetainedContinuumLimitPupil
open YM YM.Integration
open Climb Lattice Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction
open WilsonOriginalAllOrderCourse WilsonOriginalOpticalSchedule
open scoped Classical Topology

variable {G : Gauge} (R : Run G) (simple : G.Simple)

/-- The published pupil keeps the matrix, the reader and the first extension on
the same physical daughter. Its staff is chosen from that daughter's paid panels. -/
theorem original {a : Axis} {ε : ℝ} {s : WilsonOriginalAllOrderCourse.Schedule G}
    {T : Campaign R} {W : Campaign.Pillars R T}
    (paid : WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (cohort : Ultrafilter (ℕ × ℕ) → Prop)
    (issued : ∀ (f : Extraction.Order) (l : Ultrafilter (ℕ × ℕ)),
      (l : Filter (ℕ × ℕ)) ≤ f.fuse → cohort l)
    (v : Extraction.Order) :
    ∃ (M : Election.PRAY R simple) (w : Extraction.Order) (X : Scaling M.S),
      M.f = v.refine w ∧ Pert.FirstExtension M.last X ∧
      (M.Y : Filter (ℕ × ℕ)) ≤ (v.refine w).fuse ∧ cohort M.Y ∧
      Log.MatrixTicket (C := R.family) M.S M.last.sector.derivatives (M.Y : Filter (ℕ × ℕ)) ∧
      SingleLog M.last M.P.port ∧ LogTrace M.last M.P.port ∧
      Trace.Target.Result.{u} M.last simple ∧ Trace.Target.Exclusion.{u} M.last := by
  obtain ⟨w, S, F, L, Q, X, trackU, trackP, first, done, result, exclude, fac,
    foundation, single, H, Z, l, bliss, _P, _P', _J, _φ, _a, _d, _e,
    _grade, _scheme, _comp, _lead, _obedient, lies, chosen, matrix, trace⟩ :=
    PostedMatrixRetainedContinuumLimitOrder.original.{u} R simple paid cohort issued v
  obtain ⟨day, rises, roomy⟩ :=
    WilsonPhysicalWeakWallStaff.ReStaff.mile simple F H bliss trackP trackU paid.panels
  let M : Election.PRAY R simple :=
    ⟨v.refine w, S, F, trackU, trackP, fac, H, l, Z, bliss, day, rises, roomy,
      L, Q, done, foundation⟩
  exact ⟨M, w, X, rfl, first, lies, chosen, matrix, single, trace, result, exclude⟩

end IssuedBridge.PostedElectedMatrixRetainedContinuumLimitPupil
