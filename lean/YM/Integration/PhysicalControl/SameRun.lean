import YM.FVAAlt2.Moving.Supplier
import YM.EveryPhase.Summit

/-!
Typed consumer for the fixed source snapshot,
assembled over one source tree. It does not identify two
independently chosen Runs: every-phase reconstruction is applied directly to
the Final witnesses supplied by procurement on that same Run.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.PhysicalControlEstimates
open Lattice Precision RG PhysicalNext.Repeat.Legato
open YM.FVAAlt2
open Moving
open MS MS.Land
open Extraction

/-- The same Run supplies the formal correlations and, for each Final
obtained after refinement, a completed every-phase almanac. -/
theorem sameRunEveryPhase {G : Gauge} (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) :
    ∃ (C : Run G) (K : KernelChoices) (Y : Oracle.Program K)
      (Z : ∀ P : Patch, P.Branches K G) (R : Lodge.Contract C Y Z),
      C.family.path.levels.clock.kernel.penalty = ε ∧
      Run.Ties C ∧
      (∀ v : Extraction.Order,
        ∃ (w : Extraction.Order) (S : Table C.family.book)
          (F : Spec.Final C.family (v.refine w) S)
          (L : EveryPhase.Almanac F), EveryPhase.Completed F L) ∧
      Nonempty G.ColorIndex ∧
      ∃ (A : Booked (Home.seats (Study.Plan C).liftOff (Study.Plan C).certified))
        (H : MS_Data G A)
        (T : MS.Land.Prescription
          (Home.seats (Study.Plan C).liftOff (Study.Plan C).certified)),
        Moving.Supplier.CorrelationMatch Y Z C R H T := by
  obtain ⟨C, K, Y, Z, R, hpenalty, hties, hfinal, hcolor, hcomparison⟩ :=
    Moving.Supplier.procurement hG hε
  refine ⟨C, K, Y, Z, R, hpenalty, hties, ?_, hcolor, hcomparison⟩
  intro v
  obtain ⟨w, S, ⟨F⟩⟩ := hfinal v
  obtain ⟨L, hL⟩ := EveryPhase.all_characters F
  exact ⟨w, S, F, L, hL⟩

/-- A concrete consequence in the existing frozen target type. -/
theorem originalExistence : Spec.CLOSED := by
  intro G hG
  obtain ⟨C, _, _, _, _, _, _, hfinal, _, _⟩ :=
    sameRunEveryPhase hG (ε := 1) (by norm_num)
  obtain ⟨w, S, F, _, _⟩ := hfinal Extraction.Order.full
  exact ⟨C.family, Extraction.Order.full.refine w, S, ⟨F⟩⟩

end YM.RegulatorIR.FVAAlt2.PhysicalControlEstimates

