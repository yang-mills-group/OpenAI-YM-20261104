import YM.EveryPhase.Extension
import YM.MergeProof.Summit
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase
open Spec
/-- Followup 2 endpoint, on a Wilson construction. Baseline retained unchanged. -/
theorem extension : ∀ G : Gauge, G.Simple → ∃ (C : Family G) (f : Extraction.Order) (S : Table C.book)
    (F : Final C f S) (L : Almanac F), Completed F L := by
  intro G h; obtain ⟨C,f,S,⟨F⟩⟩ := MergeProof.Acme.summit G h
  exact ⟨C,f,S,F,all_characters F⟩
end YM.EveryPhase
