import YM.Integration.WilsonPositionScaleLawColorPhysicalRay
import YM.Integration.WilsonPositionScaleLawPhysicalClockRatio
import YM.Integration.WilsonMeasuredSignedActionTraceCocycle

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawPhysicalClockTransfer
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

open Next.Rank OJoint WilsonMeasuredPublicEntranceMarkedQuadratics WilsonMeasuredPublicEntranceQuadraticFiled
variable [RangeSpec] {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (J : ℝ → tower S) (simple : G.Simple) (lead : Leading F J)
    {g b : ℝ→ℝ} (cal : TendC F (fun r=>J r 4) b) (heat : Coupling G g)
def fuel (b : ℝ→ℝ) (z : ℝ×Ratio) : ℂ := ((b z.1 / b (z.2.val*z.1) : ℝ):ℂ)
include simple lead cal heat in
theorem original {d:ℕ} (up : 4≤d) :
    let w := (scheme C.labels).rise up (stepField C)
    (∀ᶠ z:ℝ×Ratio in sweep, 0 < b z.1 / b (z.2.val*z.1) ∧
      change J d z.1 z.2.val (positive z.2) w = fuel b z • w) ∧
    Tendsto (fun z:ℝ×Ratio => change J d z.1 z.2.val (positive z.2) w) sweep (𝓝 w) := by
  intro w
  have cash := WilsonMeasuredSignedActionTraceCocycle.original F J simple cal heat
  have put : ∀ᶠ z:ℝ×Ratio in sweep, 0 < b z.1 / b (z.2.val*z.1) ∧
      change J d z.1 z.2.val (positive z.2) w = fuel b z • w := by
    filter_upwards [WilsonPositionScaleLawGuardNest.natural F J lead up,cash] with z placed actual
    refine ⟨actual.1,?_⟩
    rw [show w=(scheme C.labels).rise up (stepField C) from rfl,placed,
      show change J 4 z.1 z.2.val (positive z.2) (stepField C)=fuel b z • stepField C from actual.2,map_smul]
  refine ⟨put,?_⟩
  have price := WilsonPositionScaleLawPhysicalClockRatio.original F J simple cal heat
  have scalar : Tendsto (fuel b) sweep (𝓝 (1:ℂ)) := by
    rw [show fuel b = Complex.ofReal ∘ (fun z : ℝ×Ratio => b z.1 / b (z.2.val*z.1)) from rfl]
    simpa only [Complex.ofReal_one] using (Complex.continuous_ofReal.continuousAt.tendsto.comp price)
  have target : Tendsto (fun z:ℝ×Ratio=>fuel b z • w) sweep (𝓝 w) := by
    simpa using scalar.smul (tendsto_const_nhds (x:=w))
  exact target.congr' (put.mono (fun _ h=>h.2.symm))
end YM.Integration.WilsonPositionScaleLawPhysicalClockTransfer
end
