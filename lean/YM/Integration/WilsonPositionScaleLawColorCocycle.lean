import YM.Integration.WilsonPositionScaleLawColorLive
import YM.Integration.WilsonPositionScaleLawColorActor

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawColorCocycle
open Function Filter Set Spec Table Extraction OPE Climb Trace.Pilot PhysMS Maxwell Maxwell.Free
open XSpace XSpace.Stab XSpace.Normalize MS MS.Land FVA2 FVA2.Dframe FVA2.Position.OpenAxis
open WilsonPhysicalPositionDiscreteBranches (field)
open WilsonPhysicalPositionBornCandidates (possible)
open WilsonPhysicalPositionBornTransition (present)
open WilsonPositionScaleLawColorReading (reader Bill)
open WilsonPositionThermometerGradedSource (source)
open WilsonPhysicalPositionUniformBranches (change)
open WilsonPositionScaleLawCompactNative (positive)
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawCompactBranch
open WilsonPositionScaleLawColorAtHome (Quote)
open WilsonPositionPrescribedFormalTest (raw)
open scoped Topology Classical
open WilsonPositionScaleLawColorActor (Cone Faculty)
open WilsonPositionScaleLawColorLive (Original)
variable {G : Gauge}

theorem original [RangeSpec] [PreconnectedSpace G.El] (C : Family G) (simple : G.Simple) :
    ∃ z : Fin 3 → G.Color,
      (∀ (s : Rose.Badge), (0:Fin 3)∈s → 0 < (reader C z (source C s 0)).re) ∧
      ∀ {f : Extraction.Order} {S : Table C.book} (F : Final C f S)
        (J : ℝ → tower S), Leading F J → ∀ {d : ℕ} (h : 6 ≤ d) (s : Rose.Badge),
        (0:Fin 3)∈s → ∀ {B : ℝ} (a : MoveSpace G d), a ∈ possible C d B →
        Cone C h a → ∀ {I : Type*} {l : Filter I} [NeBot l] (dates : I → ℝ × Ratio),
        Tendsto dates l sweep →
        Tendsto (fun i => change J d (dates i).1 (dates i).2.val (positive (dates i).2)
          ((scheme C.labels).rise h (source C s 0))) l
          (𝓝 (present (C:=C) (field a) ((scheme C.labels).rise h (source C s 0)))) →
        Original z s (fun i => change J 6 (dates i).1 (dates i).2.val (positive (dates i).2) (source C s 0)) l →
        Faculty F J B a := by
  obtain ⟨z,nominal,position⟩ := WilsonPositionScaleLawColorActor.original C simple
  refine ⟨z,nominal,?_⟩
  intro f S F J lead d h s upper B a chosen four I l live dates home arrived hearing
  exact position F J lead h s upper a chosen four
    (WilsonPositionScaleLawColorLive.reporter F J lead z s h a dates home arrived hearing)

end YM.Integration.WilsonPositionScaleLawColorCocycle
end
