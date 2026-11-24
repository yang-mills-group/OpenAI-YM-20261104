import YM.Integration.WilsonPositionScaleLawMeasuredMoves
import YM.Integration.WilsonPositionScaleLawMeasuredAxes
import YM.Integration.WilsonPositionScaleLawMeasuredIFT
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotRestriction
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredJoint
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


open scoped ContDiff
open WilsonPositionProgramTrialPublicJointPivotRestriction (coordinates)
open WilsonPositionScaleLawMeasuredBank (fixed)
variable {d : ℕ}
def reduce (h:6≤d) (x:MoveSpace G d×ℝ) : MoveSpace G 6×ℝ := (coordinates h x.1,x.2)
def full (h:6≤d) (q:ℕ) (x:MoveSpace G d×ℝ) : MoveSpace G d×ℝ :=
  (WilsonPositionScaleLawMeasuredBank.fields Z M ν d (q+1) x,
    WilsonPositionScaleLawMeasuredBank.signed Z M H ν q (reduce h x))
theorem inclusion (h:6≤d) (x:MoveSpace G d) (p:Sec G 6) :
    up h (Fray.box (coordinates h x) p)=Fray.box x (up h p) := by
  obtain ⟨T,rfl⟩:=(guide G d).surjective x
  simp only [Fray.box,WilsonPositionProgramTrialPublicJointPivotRestriction.guided,LinearEquiv.symm_apply_apply]
  exact WilsonPositionProgramTrialPublicJointPivotRestriction.original h T p
theorem smooth (h:6≤d)(q:ℕ) : ContDiff ℝ ω (full Z M H ν h q) :=
  (WilsonPositionScaleLawMeasuredFields.smooth Z M ν d (q+1)).prodMk
    ((WilsonPositionScaleLawMeasuredMoves.thermometer Z M H ν q).comp (((coordinates h).contDiff.comp contDiff_fst).prodMk contDiff_snd))
theorem axis (h:6≤d)(q:ℕ)(t:ℝ) : full Z M H ν h q (0,t)=(fixed Z d,t) := by
  apply Prod.ext (WilsonPositionScaleLawMeasuredBank.horizontal Z M H ν d (q+1) t)
  change WilsonPositionScaleLawMeasuredBank.signed Z M H ν q (coordinates h 0,t)=t
  rw [map_zero,WilsonPositionScaleLawMeasuredBank.thermometer Z M H ν q t]
theorem derivative (h:6≤d)(q:ℕ)
    (zero:∀x:MoveSpace G 6,WilsonPositionScaleLawMeasuredBank.signed Z M H ν q (x,0)=0) :
    fderiv ℝ (full Z M H ν h q) 0=1 := by
  apply WilsonPositionScaleLawMeasuredAxes.matrix _ (smooth Z M H ν h q)
  · have right : HasFDerivAt (𝕜:=ℝ) (fun x:MoveSpace G d=>(full Z M H ν h q (x,0)).2) 0 0 := by
      change HasFDerivAt (𝕜:=ℝ) (fun x:MoveSpace G d=>WilsonPositionScaleLawMeasuredBank.signed Z M H ν q (coordinates h x,0)) 0 0
      simp_rw [zero]
      exact hasFDerivAt_const _ _
    exact (WilsonPositionScaleLawMeasuredFields.ground Z M H ν d (q+1)).prodMk right
  · have paid : (fun t:ℝ=>full Z M H ν h q (0,t))=fun t:ℝ=>(fixed Z d,t) := funext (axis Z M H ν h q)
    rw [paid]
    have constant : HasFDerivAt (𝕜:=ℝ) (fun _:ℝ=>fixed Z d) 0 0 := hasFDerivAt_const _ _
    exact constant.prodMk (hasFDerivAt_id (𝕜:=ℝ) (0:ℝ))
end YM.Integration.WilsonPositionScaleLawMeasuredJoint
