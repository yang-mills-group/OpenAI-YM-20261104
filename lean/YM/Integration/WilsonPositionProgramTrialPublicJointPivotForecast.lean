import YM.Integration.WilsonPositionProgramTrialPublicJointPivotThermometer

/-! Polynomial position data on the already prescribed independent section and its true free starting value. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotForecast
open Filter Function Finset Set MeasureTheory Lattice RG PhysicalNext.Repeat.Legato
open RG17 FullVolume OPE OPE.Orbits Climb Next.UVStress FVA2 FVA2.Register Trace.Target
open Spec Table Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize PhysMS
open WilsonPhysicalNormalizedSignedMenu (Row offered docket retag)
open WilsonPhysicalPositionTargetRows (rows)
open WilsonPositionPrescribedScreen (hierarchy)
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

def forecast (d q : ℕ) (g : ℝ) : Prediction G d := fun n =>
  ∑ k ∈ range (q+1), (g:ℂ)^k • (Reg.Faith.reports ν Z.criterion M d k n)

theorem value (d q : ℕ) (g : ℝ) {n : ℕ} (t : Test n) (p : Fin n → Sec G d) :
    forecast Z M ν d q g n t p = ∑ k ∈ range (q+1), (g:ℂ)^k * Reg.Faith.reports ν Z.criterion M d k n t p := by
  simp only [forecast,LinearMap.sum_apply,_root_.sum_apply,LinearMap.smul_apply,_root_.smul_apply,smul_eq_mul]

include H in
theorem earned (d : ℕ) : Reg.Faith.reports ν Z.criterion M d 0 = reference G d := by
  let data := H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  change realm (liftT Z.criterion ν M d) _ 0 = _
  rw [Normalize.rest,pay0,(Measure.charges Z.scheme Z.criterion ν M σ (d:=d) hG data.Taylor data.still data.base).zero,
    Screen.recruit_one,Reg.State.freeT]

include H in
theorem prescribed (d k n : ℕ) (t : Test n) (p : Fin n → Sec G d) :
    Reg.Faith.reports ν Z.criterion M d k n t p =
      t.applyTo (fun x => Jury.fxt (Measure.start Z.scheme Z.criterion d) x k p) := by
  let data := H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  exact (Jury.enrolled ν M Z.scheme Z.criterion σ hG data.Taylor data.still data.base (d:=d)).exact n k t p

include H in
theorem actual (k n : ℕ) (t : Test n) (p : Fin n → Sec G 6) :
    Reg.Faith.reports ν Z.criterion M 6 k n t p =
      t.applyTo (fun x => Jury.fxt (response Z M ν 0) x k p) := by
  rw [WilsonPositionScaleLawThermometerChart.response,WilsonPositionScaleLawThermometerOrigin.clock Z M H ν,Facets.team_one]
  exact prescribed Z M H ν 6 k n t p

include H in
theorem zero (d q : ℕ) : forecast Z M ν d q 0 = reference G d := by
  rw [← earned Z M H ν d]
  ext1 n
  ext1 t
  ext1 p
  rw [value]
  simp [zero_pow_eq]

include H in
theorem original {ι : Type*} (u : Filter ι) (d q : ℕ) (g : ι → ℝ) (small : Tendsto g u (𝓝 0)) :
    (Z.store.survey d).Via (fun i => forecast Z M ν d q (g i)) (u:=u) := by
  apply tendsto_pi_nhds.mpr
  intro h
  apply tendsto_pi_nhds.mpr
  intro j
  let t := (Z.store.survey d).scope h
  let p (i : Fin t.n) := Module.finBasis ℝ (Sec G d) (j i)
  change Tendsto (fun i => forecast Z M ν d q (g i) t.n t.t p) u (𝓝 (reference G d t.n t.t p))
  rw [←zero Z M H ν d q]
  have continuous : Continuous (fun v:ℝ => forecast Z M ν d q v t.n t.t p) := by
    simp_rw [value]
    fun_prop
  exact continuous.continuousAt.tendsto.comp small

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotForecast
