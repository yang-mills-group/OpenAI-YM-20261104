import YM.Integration.WilsonOriginalSeparatedCourse
import YM.GapsContact.Earn.Buoys

/-! The original reflected public sources and the matrix ticket on a single extraction. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalSeparatedPublicFields
open Climb Lattice Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction GapsContact.Seams
open scoped Classical Topology
variable {G : Gauge} {R : Run G} {simple : G.Simple}

/-- Each finite horizon uses one pair of dates for every public field below the
horizon. `Pool.budget` and `Turnkey.coin` give the measured quota and the
reflected card of the very same microscopic representative. -/
theorem pooled {cohort : Ultrafilter (ℕ × ℕ) → Prop}
    (elected : WilsonMacroscopicFundedReader.Elected.{u} R simple cohort) (v : Extraction.Order) :
    ∃ (w : Extraction.Order) (S : Table R.family.book) (F : Final R.family (v.refine w) S)
      (Q : Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
      (Y : (Bel R.family.book).Hierarchy) (Z : Trace.Terrace.Arch R.family)
      (l : Ultrafilter (ℕ × ℕ)) (_ : Bliss F l Z Y) (J : ℝ → PhysMS.tower S),
      Facilities R.family (v.refine w) S ∧ Orbits.Foundation F Q ∧ SingleLog F Q.port ∧
      Leading F J ∧ (∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d) ∧
      (l : Filter (ℕ × ℕ)) ≤ (v.refine w).fuse ∧ cohort l ∧
      Log.MatrixTicket (C := R.family) S F.sector.derivatives (l : Filter (ℕ × ℕ)) ∧
      ∀ d, ∃ t : ℕ, ∀ᶠ r in trail, ∃ j m, Pool F l r j m d (dock r ^ t) := by
  obtain ⟨w, S, F, _, Q, _, _, _, facilities, foundation, spatial, Y, Z, l, bliss,
    _, _, J, _, _, _, _, _, _, _, leading, obedient, lies, selected, matrix⟩ := elected v
  exact ⟨w, S, F, Q, Y, Z, l, bliss, J, facilities, foundation, spatial, leading,
    obedient, lies, selected, matrix, fun d => every_pool F simple bliss d⟩

end YM.Integration.WilsonOriginalSeparatedPublicFields
end

