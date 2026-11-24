import YM.Integration.WilsonPositionScaleLawMeasuredBank
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredFields
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
open WilsonPositionScaleLawMeasuredBank (fields)
theorem purse (d q : ℕ) : ContDiff ℝ ω (fun u : ℝ => (Z.store.survey d).purse (forecast Z M ν d q u)) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro b
  change ContDiff ℝ ω (fun u : ℝ => forecast Z M ν d q u _ _ _)
  simp_rw [WilsonPositionProgramTrialPublicJointPivotForecast.value]
  apply ContDiff.sum
  intro k _
  exact (Complex.ofRealCLM.contDiff.pow k).mul contDiff_const
theorem smooth (d q : ℕ) : ContDiff ℝ ω (fields Z M ν d q) := by
  let D:=Z.store.survey d
  have same : fields Z M ν d q=fun x:MoveSpace G d × ℝ=>D.itinerary (D.purse (forecast Z M ν d q x.2),x.1) :=
    funext fun x=>(D.way _ _).symm
  rw [same]
  exact D.fair.comp (((purse Z M ν d q).comp contDiff_snd).prodMk contDiff_fst)
include H in
theorem ground (d q : ℕ) : HasFDerivAt (fun x:MoveSpace G d=>fields Z M ν d q (x,0))
      (ContinuousLinearMap.id ℝ (MoveSpace G d)) 0 := by
  let D:=Z.store.survey d
  have same : (fun x:MoveSpace G d=>fields Z M ν d q (x,0)) =
      D.itinerary ∘ (fun x:MoveSpace G d=>(D.opening.1,x)) := by
    funext x
    change guide G d ((Z.store.measure d).D (recruit (Fray.box x) (forecast Z M ν d q 0))) = _
    rw [WilsonPositionProgramTrialPublicJointPivotForecast.zero Z M H ν]
    exact (D.way _ _).symm
  have embed : HasFDerivAt (fun x:MoveSpace G d=>(D.opening.1,x))
      (ContinuousLinearMap.inr ℝ D.Bag (MoveSpace G d)) 0 :=
    (hasFDerivAt_const D.opening.1 (0:MoveSpace G d)).prodMk (hasFDerivAt_id _)
  rw [same]
  change HasFDerivAt _ (1:MoveSpace G d→L[ℝ]MoveSpace G d) 0
  rw [←D.unpin (Z.store.prepared d)]
  exact (D.fair.differentiable (by simp) D.opening).hasFDerivAt.comp 0 embed
end YM.Integration.WilsonPositionScaleLawMeasuredFields
