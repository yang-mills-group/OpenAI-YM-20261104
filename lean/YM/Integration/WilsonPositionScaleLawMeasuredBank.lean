import YM.Integration.WilsonPositionProgramTrialPublicJointPivotPrepositioned
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotTarget
import YM.Integration.WilsonPositionScaleLawThermometerOrigin
import YM.Integration.WilsonPositionHomogeneousFrame
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredBank
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


def fields (d q : ℕ) (x : MoveSpace G d × ℝ) : MoveSpace G d :=
  guide G d ((Z.store.measure d).D (recruit (stand ((guide G d).symm x.1)) (forecast Z M ν d q x.2)))
def signed (q : ℕ) (x : MoveSpace G 6 × ℝ) : ℝ :=
  ((WilsonPositionProgramTrialPublicJointPivotTarget.row Z M H ν 0 (q+1) (x.2:ℂ))
    (fun i=>stand ((guide G 6).symm x.1) (Rose.tag G i))).re / Rose.cT Z.criterion.cut G Z.criterion.image
def joint (q : ℕ) (x : MoveSpace G 6 × ℝ) : MoveSpace G 6 × ℝ := (fields Z M ν 6 (q+1) x,signed Z M H ν q x)
def fixed (d : ℕ) : MoveSpace G d := guide G d ((Z.store.measure d).D (reference G d))
include H in
theorem horizontal (d q : ℕ) (u : ℝ) : fields Z M ν d q (0,u)=fixed Z d := by
  exact congrArg (guide G d) (by
    simpa only [Fray.SetEq,map_zero] using WilsonPositionProgramTrialPublicJointPivotPrepositioned.bank Z M H ν d q u)
theorem thermometer (q : ℕ) (u : ℝ) : signed Z M H ν q (0,u)=u := by
  unfold signed
  simp only [map_zero,stand0,Module.End.one_apply]
  rw [WilsonPositionProgramTrialPublicJointPivotTarget.original,WilsonPositionScaleLawThermometerOrigin.clock Z M H ν,WilsonPositionScaleLawThermometerOrigin.initial]
  simp [Complex.mul_re,Z.criterion.fresh.ne]
theorem diagonal (q : ℕ) (u : ℝ) : joint Z M H ν q (0,u)=(fixed Z 6,u) :=
  Prod.ext (horizontal Z M H ν 6 (q+1) u) (thermometer Z M H ν q u)
end YM.Integration.WilsonPositionScaleLawMeasuredBank
