import YM.TraceExtension.Endpoint
import YM.EveryPhase.Summit

/-!
# Trace and reconstruction on one Wilson family

The trace and spectral conclusions use the selected vacuum of `Final`.
The phase reconstruction applies to every character phase of that same
continuum table.
-/

set_option autoImplicit false

namespace YM.Trace.Target

universe u

/-- A common calibrated Wilson construction and order refinement support the selected-vacuum trace result and reconstruction of every character phase. -/
theorem with_every_phase (G : Gauge) (h : G.Simple) (b : ℝ) (hb : 0 < b)
    (p : Extraction.Order) :
    ∃ C : Family G, C.Makes ∧ Spec.Calibrated C ∧
      C.path.levels.clock.kernel.penalty = b ∧ Extraction.Wcmain C ∧
      ∃ (q : Extraction.Order) (S : Table C.book)
        (F : Spec.Final C (p.refine q) S),
        Result.{u} F h ∧ ∃ L : EveryPhase.Almanac F, EveryPhase.Completed F L := by
  obtain ⟨C, hC, hK, hB, hW, q, ⟨S, ⟨F⟩⟩, hF⟩ := main.{u} G h b hb p
  exact ⟨C, hC, hK, hB, hW, q, S, F, hF S F, EveryPhase.all_characters F⟩

end YM.Trace.Target
