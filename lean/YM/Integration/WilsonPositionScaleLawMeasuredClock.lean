import YM.Integration.WilsonPositionScaleLawMeasuredJoint
import YM.Integration.WilsonObservedChiralFreeFiledThermometer
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotRoseGround
import YM.Integration.WilsonPositionScaleLawMeasuredIFT
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredClock
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
open WilsonPositionScaleLawMeasuredJoint (full)
theorem ground (q:ℕ) (x:MoveSpace G 6) :
    WilsonPositionScaleLawMeasuredBank.signed Z M H ν q (x,0)=0 := by
  unfold WilsonPositionScaleLawMeasuredBank.signed
  simp only [Complex.ofReal_zero]
  rw [WilsonPositionProgramTrialPublicJointPivotRoseGround.original,
    WilsonObservedChiralFreeFiledThermometer.original Z hG ((guide G 6).symm x)]
  simp
theorem jacobian (h:6≤d)(q:ℕ) : fderiv ℝ (full Z M H ν h q) 0=1 :=
  WilsonPositionScaleLawMeasuredJoint.derivative Z M H ν h q (ground Z M H ν q)
theorem live (h:6≤d)(q:ℕ) : (fderiv ℝ (full Z M H ν h q) 0).IsInvertible := by
  rw [jacobian Z M H ν h q]
  exact ContinuousLinearMap.isInvertible_equiv (f:=ContinuousLinearEquiv.refl ℝ _)
theorem localBound (h:6≤d)(q:ℕ) :
    ∀ᶠz in 𝓝 (0:MoveSpace G d×ℝ),∃A:(MoveSpace G d×ℝ)≃L[ℝ](MoveSpace G d×ℝ),
      A.toContinuousLinearMap=fderiv ℝ (full Z M H ν h q) z ∧ ‖A.symm.toContinuousLinearMap‖≤2 :=
  WilsonPositionScaleLawMeasuredAxes.quantitative _ (WilsonPositionScaleLawMeasuredJoint.smooth Z M H ν h q) _ (jacobian Z M H ν h q)
def chart (h:6≤d)(q:ℕ) : (MoveSpace G d×ℝ)→MoveSpace G d×ℝ :=
  WilsonPositionScaleLawMeasuredIFT.elected _ (WilsonPositionScaleLawMeasuredJoint.smooth Z M H ν h q) 0 (live Z M H ν h q)
theorem measured (h:6≤d)(q:ℕ) : ∀ᶠt:ℝ in 𝓝 0, chart Z M H ν h q (fixed Z d,t)=(0,t) := by
  let D:=full Z M H ν h q
  have path:Tendsto (fun t:ℝ=>((0:MoveSpace G d),t)) (𝓝 0) (𝓝 0) := tendsto_const_nhds.prodMk_nhds tendsto_id
  filter_upwards [path.eventually (WilsonPositionScaleLawMeasuredIFT.recovers D
    (WilsonPositionScaleLawMeasuredJoint.smooth Z M H ν h q) 0 (live Z M H ν h q))] with t ht
  simpa only [D,chart,WilsonPositionScaleLawMeasuredJoint.axis] using ht
end YM.Integration.WilsonPositionScaleLawMeasuredClock
