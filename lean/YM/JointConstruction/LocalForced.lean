import YM.LocalTaylorR2.Sails.Deeper
import YM.RG12Sharp.Mark.Shell

/-!
# Local Taylor estimates and forced inheritance on one actual family

The local Taylor constructor explicitly returns a Floral witness. This module
uses that witness to apply the forced-inheritance result
to exactly the same family, history, coupling, labels, and local sections.

This does not assert the full local comparison lemma. In particular, the
input Format/remBound conditions remain explicit, and no identification with
independent formal Wilson coefficients is introduced here.
-/

set_option autoImplicit false
noncomputable section

namespace YM.JointConstruction

open Source MergeProof

/-- The actual forced-insertion step, uniformly over its stated admissible
scales, periods, cutoffs, and label horizons, on a fixed family. -/
def ForcedStepControl {G : Gauge} (C : Family G) : Prop :=
  ∀ (d N p m : ℕ), d ≤ C.path.levels.clock.J m → m < N →
    ∀ (T : Coefficient (C.labels.level d) (C.S.side (m + 1) p)) (b : ℝ),
      T.Format 0 C.params (C.path.rep N p (m + 1)) →
      T.remBound 0 (C.path.rep N p (m + 1))
        (Real.sqrt (C.path.levels.clock.forcedAllowance (m + 1))) b →
      let a := Extra.Histories.Doors.rate (C.S.block m) *
        Real.sqrt (C.path.levels.clock.forcedAllowance (m + 1)) * b
      ∃ P, Gig (C.localSection d) C.path N p m C.params
        (RG12Sharp.Clamp.inheritance (C.path.rep N p (m + 1)) T) P 0 a a

theorem forcedStepControl_of_floral {G : Gauge} (C : Family G) (g : G.Simple)
    (hC : UVExtension.Oasis.Floral (hG := g) C) : ForcedStepControl C := by
  intro d N p m hd hm T b ht hb
  exact RG12Sharp.Clamp.recorded C g hC hd hm T b ht hb

/-- One construction simultaneously retains the local Taylor package and the
actual forced-inheritance estimate. No two existential families are equated. -/
theorem localTaylor_with_forcedInheritance {G : Gauge} (g : G.Simple)
    (κ : ℝ) (hκ : 0 < κ)
    (δ : PhysicalNext.Repeat.Daisy.Charity.RG12.Decal G) (F : Extraction.Order) :
    ∃ (C : Family G) (f : Extraction.Order) (T : Table C.book)
      (W : Spec.Final C (F.refine f) T) (L : EveryPhase.Almanac W)
      (A : UVExtension.Mast.Couture C g
        (LocalTaylorR2.Marigold.aetherD (LocalTaylorR2.Strange.jetEngine G) δ)),
      C.Makes ∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty = κ ∧
      UVExtension.Oasis.Floral (hG := g) C ∧
      (Extraction.Order.mk Extraction.Sequence.full (F.refine f).per).Ordered C T ∧
      EveryPhase.Completed W L ∧ OPE.Facilities C (F.refine f) T ∧
      LocalTaylorR2.Marigold.QuadPose (LocalTaylorR2.Strange.jetEngine G) A ∧
      ForcedStepControl C := by
  obtain ⟨C, f, T, W, L, A, hC, hCal, hPenalty, hFloral, hOrdered, hPhase,
    hFacilities, hTaylor⟩ := LocalTaylorR2.Marigold.violine g κ hκ δ F
  exact ⟨C, f, T, W, L, A, hC, hCal, hPenalty, hFloral, hOrdered, hPhase,
    hFacilities, hTaylor, forcedStepControl_of_floral C g hFloral⟩

end YM.JointConstruction
