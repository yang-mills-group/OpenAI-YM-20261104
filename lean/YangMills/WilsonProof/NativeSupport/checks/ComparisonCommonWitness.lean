import YM.UVExtension.Reports.Ultraviolet
import YM.EveryPhase.Extension

/-!
# Candidate common UV/every-phase witness check

Package-owned source-only check, outside the accepted FOLLOWUP source manifest.
This composition has not yet been compiled or independently accepted. It changes
no accepted module and is not imported by `YM.lean`.

The same `C`, `f`, `T` and chosen `F` carry every conclusion below. The full-mesh
ordered statement does not replace the extraction order of that `F`. All domains
and meanings of `Floral`, `Margins` and `Completed` remain those of their APIs.
-/

set_option autoImplicit false
noncomputable section

namespace YM.ComparisonPackage

open Filter

/-- Compose the accepted providers without choosing another physical witness. -/
theorem common_uv_every_phase
    (G : Gauge) (hG : G.Simple) (penalty : ℝ) (hp : 0 < penalty) :
    ∃ (C : Family G) (f : Extraction.Order) (T : Table C.book)
      (F : Spec.Final C f T) (L : EveryPhase.Almanac F),
      C.Makes ∧ Spec.Calibrated C ∧
      C.path.levels.clock.kernel.penalty = penalty ∧
      UVExtension.Oasis.Floral (hG := hG) C ∧
      (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T ∧
      (∀ d k : ℕ, ∀ᶠ n in atTop,
        ∀ (r : ℕ) (v : Fin r → C.book.Token), (∀ i, (v i).1 ≤ d) →
          ∃ g, UVExtension.Poppy.Margins C r n k v g) ∧
      EveryPhase.Completed F L := by
  obtain ⟨C, f, T, hFinal, hMakes, hCalibrated, hPenalty, hFloral,
    hOrdered, hMargins⟩ := UVExtension.Reports.ultraviolet G hG penalty hp
  obtain ⟨F⟩ := hFinal
  obtain ⟨L, hCompleted⟩ := EveryPhase.all_characters F
  exact ⟨C, f, T, F, L, hMakes, hCalibrated, hPenalty, hFloral,
    hOrdered, hMargins, hCompleted⟩

end YM.ComparisonPackage

