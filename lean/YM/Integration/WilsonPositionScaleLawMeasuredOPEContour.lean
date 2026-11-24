import YM.Integration.WilsonPositionScaleLawMeasuredClock
import YM.Integration.WilsonPositionScaleLawMeasuredContour
import YM.Integration.WilsonPositionScaleLawMeasuredOPE
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredOPEContour
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

open WilsonPositionScaleLawMeasuredJoint (full)
open WilsonPositionScaleLawMeasuredOutput (field)
open WilsonPositionScaleLawMeasuredContour (contrast)
theorem original (d:ℕ)(six:6≤d)(order:ℕ):
    ∃δ:ℝ,0<δ ∧ ∀ᶠbase in 𝓝 (0:MoveSpace G d×ℝ),
      ∀w∈Metric.ball ((full Z M H ν six order) 0) δ,
      ∀j:Fin (d+1),∀q m:ℕ,∀φ:Test m,∀v:Fin m→Sec G d,∀μ:Toon G j→ℂ,∀cash:ℂ,
        let D:=full Z M H ν six order
        let rev:=WilsonPositionScaleLawMeasuredClock.chart Z M H ν six order
        let O:=WilsonPositionScaleLawMeasuredOPE.row Z M ν (Nat.le_of_lt_succ j.isLt) q φ v μ
        contrast D O rev base w cash=cash-O (rev w) := by
  let D:=full Z M H ν six order
  have smooth:=WilsonPositionScaleLawMeasuredJoint.smooth Z M H ν six order
  have jac:=WilsonPositionScaleLawMeasuredClock.jacobian Z M H ν six order
  let valid(z:MoveSpace G d×ℝ):=∀h:Fin (d+1),(field h (coordinates (Nat.le_of_lt_succ h.isLt) z.1)).IsInvertible
  have safe:∀ᶠz in 𝓝 (0:MoveSpace G d×ℝ),valid z:=eventually_all.mpr fun h=>
    WilsonPositionScaleLawMeasuredOPE.admissible (Nat.le_of_lt_succ h.isLt)
  obtain ⟨δ,positive,paid⟩:=WilsonPositionScaleLawMeasuredContour.localized (V:=ℂ) D smooth 0 jac valid safe
  refine ⟨δ,positive,?_⟩
  filter_upwards [paid] with base pre w hw j q m φ v μ cash
  exact pre.2 w hw _ (fun x hx=>WilsonPositionScaleLawMeasuredOPE.regular Z M ν _ q φ v μ x (hx j)) cash

end YM.Integration.WilsonPositionScaleLawMeasuredOPEContour
