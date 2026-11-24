import YM.Integration.WilsonPositionScaleLawMeasuredRows
import YM.Integration.WilsonPositionScaleLawMeasuredFields
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredMoves
open WilsonPhysicalRosePositionFace (located predicted)
open WilsonPositionProgramTrialPublicJointPivotRose (Live tested)
open scoped Classical Topology BigOperators
open Function Filter Set Finset PowerSeries MeasureTheory Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open FVA2.Scale.Jury (Thin fxt)
open WilsonPositionScaleLawThermometerChart (response)
open WilsonPositionScaleLawIndependent (ψ)
open scoped Topology BigOperators Classical Polynomial


open Position Position.Axes Dframe Level Reg.Point Facets Equator Measure Reg.CoverTest
variable {G : Gauge} (Z : WilsonPrescription G) {hG : G.Simple}
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {b : Bool} (H : Main.Match Z hG M σ b) (ν : ℝ)
open WilsonPositionProgramTrialPublicJointPivotForecast (forecast)


open WilsonPhysicalNormalizedSignedMenu (Row)
open private ways from YM.XSpace.Panorama
open scoped ContDiff
theorem moved {d n : ℕ} (A : ℝ → Row G d n) (smooth : ∀p, ContDiff ℝ ω (fun u:ℝ=>A u p))
    (v : Fin n → Sec G d) : ContDiff ℝ ω (fun z:MoveSpace G d×ℝ=>A z.2 (fun i=>Fray.box z.1 (v i))) := by
  have eqn (z:MoveSpace G d×ℝ) := medium (fun i=>Fray.box z.1 (v i)) ((A z.2).restrictScalars ℝ)
  change ContDiff ℝ ω (fun z:MoveSpace G d×ℝ=>((A z.2).restrictScalars ℝ) (fun i=>Fray.box z.1 (v i)))
  simp_rw [eqn]
  apply ContDiff.sum
  intro r _
  apply ContDiff.smul
    (f:=fun z:MoveSpace G d×ℝ=>∏i,tableD G d (Fray.box z.1 (v i)) (r i))
    (g:=fun z:MoveSpace G d×ℝ=>A z.2 (fun i=>Module.finBasis ℝ (Sec G d) (r i)))
  · apply contDiff_prod
    intro i _
    simp_rw [Fray.box,stood,map_add]
    exact (contDiff_apply ℝ ℝ (r i)).comp (contDiff_const.add ((ways (v i)).contDiff.comp contDiff_fst))
  · exact (smooth _).comp contDiff_snd
theorem thermometer (q : ℕ) : ContDiff ℝ ω (WilsonPositionScaleLawMeasuredBank.signed Z M H ν q) := by
  let A:=fun u:ℝ=>WilsonPositionProgramTrialPublicJointPivotTarget.row Z M H ν 0 (q+1) (u:ℂ)
  have s:=moved A (fun p=>WilsonPositionScaleLawMeasuredRows.thermal Z M H ν 0 (q+1) p) (Rose.tag G)
  unfold WilsonPositionScaleLawMeasuredBank.signed
  simp only [div_eq_mul_inv]
  exact (Complex.reCLM.contDiff.comp s).mul contDiff_const
theorem ordinary (d q n : ℕ) (φ:Test n) (p:Fin n→Sec G d) :
    ContDiff ℝ ω (fun z:MoveSpace G d×ℝ=>forecast Z M ν d q z.2 n φ (fun i=>Fray.box z.1 (p i))) := by
  apply moved (fun u:ℝ=>forecast Z M ν d q u n φ) _ p
  intro v
  simp_rw [WilsonPositionProgramTrialPublicJointPivotForecast.value]
  apply ContDiff.sum
  intro k _
  exact (Complex.ofRealCLM.contDiff.pow k).mul contDiff_const
end YM.Integration.WilsonPositionScaleLawMeasuredMoves
