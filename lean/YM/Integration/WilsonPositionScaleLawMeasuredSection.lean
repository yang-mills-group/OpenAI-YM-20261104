import YM.Integration.WilsonPositionScaleLawMeasuredMoves
import YM.Integration.WilsonPositionHomogeneousComparison
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredSection
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
def reports (d:ℕ) : Reports G d := realm (Measure.adjust Z.scheme Z.criterion d) (Reg.Faith.reports ν Z.criterion M d)

include H in
theorem enrolled (d:ℕ) : Jury.Orders (Measure.outlook Z.scheme Z.criterion d) (reports Z M ν d) := by
  let base:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  exact (Jury.enrolled ν M Z.scheme Z.criterion σ hG base.Taylor base.still base.base (d:=d)).specify _

include H in
theorem registered (d k n:ℕ)(φ:Test n)(v:Fin n→Sec G d) :
    reports Z M ν d k n φ v=φ.applyTo (fun x=>if hx:x∈conf n then
      WilsonPositionHomogeneousComparison.coefficient Z M ν d ⟨x,hx⟩ v k else 0) := by
  rw [(enrolled Z M H ν d).exact n k φ v]
  apply Test.apply_eq
  intro x hx
  dsimp only
  rw [dif_pos hx,WilsonPositionHomogeneousComparison.filed Z M H ν d ⟨x,hx⟩ v k]
  change Jury.fxt _ (⟨x,hx⟩:Stage n).val k v=_
  rw [Jury.exactC]

def clipped (d q:ℕ)(u:ℝ) : Prediction G d := fun n=>∑ k∈range (q+1),(u:ℂ)^k • reports Z M ν d k n

theorem value (d q:ℕ)(u:ℝ){n:ℕ}(φ:Test n)(v:Fin n→Sec G d) :
    clipped Z M ν d q u n φ v=∑ k∈range (q+1),(u:ℂ)^k*(reports Z M ν d k n φ v) := by
  simp only [clipped,LinearMap.sum_apply,_root_.sum_apply,LinearMap.smul_apply,_root_.smul_apply,smul_eq_mul]

include H in
theorem assigned (d q:ℕ)(u:ℝ){n:ℕ}(φ:Test n)(v:Fin n→Sec G d) :
    clipped Z M ν d q u n φ v=∑ k∈range (q+1),(u:ℂ)^k*φ.applyTo (fun x=>if hx:x∈conf n then
      WilsonPositionHomogeneousComparison.coefficient Z M ν d ⟨x,hx⟩ v k else 0) := by
  rw [value]
  exact Finset.sum_congr rfl fun k _=>congrArg (fun a:ℂ=>(u:ℂ)^k*a) (registered Z M H ν d k n φ v)

theorem smooth (d q:ℕ){n:ℕ}(φ:Test n)(v:Fin n→Sec G d) :
    ContDiff ℝ ω (fun z:MoveSpace G d×ℝ=>clipped Z M ν d q z.2 n φ (fun i=>Fray.box z.1 (v i))) := by
  apply WilsonPositionScaleLawMeasuredMoves.moved (fun u:ℝ=>clipped Z M ν d q u n φ) _ v
  intro p
  simp_rw [value]
  apply ContDiff.sum
  intro k _
  exact (Complex.ofRealCLM.contDiff.pow k).mul contDiff_const

end YM.Integration.WilsonPositionScaleLawMeasuredSection
