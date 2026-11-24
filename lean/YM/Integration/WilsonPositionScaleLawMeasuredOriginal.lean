import YM.Integration.WilsonPositionScaleLawMeasuredBank
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredOriginal
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


open WilsonPositionScaleLawMeasuredBank
variable {R : Run G} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S) (J : ℝ → PhysMS.tower S)
def measured (d : ℕ) (r : ℝ) : MoveSpace G d × ℝ :=
  (guide G d ((Z.store.measure d).D (WilsonPositionPrescribedScreen.hierarchy F
    (WilsonPositionPrescribedFrame.positioned F J Z.store) d r)), WilsonPositionHomogeneousFrame.reading F J Z r)
theorem position (lead : PhysMS.Leading F J) (d : ℕ) : ∀ᶠr in trail,
    (Z.store.measure d).D (WilsonPositionPrescribedScreen.hierarchy F
      (WilsonPositionPrescribedFrame.positioned F J Z.store) d r)=(Z.store.measure d).D (reference G d) := by
  filter_upwards [WilsonPositionPrescribedFrame.measured F J Z.store lead d,
    (WilsonPositionPrescribedScreen.original F J lead Z.store d).2] with r frame earned
  rw [frame]
  exact earned.1
theorem original (lead : PhysMS.Leading F J) (q : ℕ) :
    ∀ᶠr in trail, measured Z F J 6 r = joint Z M H ν q (0,WilsonPositionHomogeneousFrame.reading F J Z r) := by
  filter_upwards [position Z F J lead 6] with r positions
  rw [WilsonPositionScaleLawMeasuredBank.diagonal]
  exact Prod.ext (congrArg (guide G 6) positions) rfl
end YM.Integration.WilsonPositionScaleLawMeasuredOriginal
