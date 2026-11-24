import YM.Integration.WilsonPositionScaleLawColorPhysicalRay
import YM.Integration.WilsonMeasuredSignedActionTraceCocycle

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawColorPhysical
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
        (J : ℝ → tower S), Leading F J → ∀ {g b : ℝ→ℝ}, TendC F (fun r=>J r 4) b → Coupling G g → ∀ {d : ℕ} (_h : 6 ≤ d) (s : Rose.Badge),
        (0:Fin 3)∈s → ∀ {B : ℝ} (a : MoveSpace G d), a ∈ possible C d B →
        ∀ {I : Type*} {l : Filter I} [NeBot l] (dates : I → ℝ × Ratio),
        Tendsto dates l sweep →
        (∀ v : (Bel C.book).Field d, Tendsto
          (fun i => change J d (dates i).1 (dates i).2.val (positive (dates i).2) v) l
          (𝓝 (present (C:=C) (field a) v))) →
        Original z s (fun i => change J 6 (dates i).1 (dates i).2.val (positive (dates i).2) (source C s 0)) l →
        Faculty F J B a := by
  obtain ⟨z,nominal,position⟩ := WilsonPositionScaleLawColorCocycle.original C simple
  refine ⟨z,nominal,?_⟩
  intro f S F J lead g b cal heat d h s upper B a chosen I l live dates home arrived hearing
  have realRay : WilsonPositionScaleLawColorPhysicalRay.Ray J :=
    (WilsonMeasuredSignedActionTraceCocycle.original F J simple cal heat).mono (fun z vote =>
      ⟨_,vote.1.le,vote.2⟩)
  have four := WilsonPositionScaleLawColorPhysicalRay.original F J lead h a realRay dates home (arrived _)
  exact position F J lead h s upper a chosen four dates home (arrived _) hearing

end YM.Integration.WilsonPositionScaleLawColorPhysical
end
