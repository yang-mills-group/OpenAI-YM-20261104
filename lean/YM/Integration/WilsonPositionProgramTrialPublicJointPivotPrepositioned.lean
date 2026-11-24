import YM.Integration.WilsonPositionProgramTrialPublicJointPivotForecast

/-! The independent polynomial already satisfies the appointed position equations at finite heat. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotPrepositioned
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
open WilsonPositionProgramTrialPublicJointPivotForecast (forecast)

include H in
theorem coefficient (d k : ℕ) :
    (Z.store.measure d).D (Reg.Faith.reports ν Z.criterion M d k) =
      if k=0 then (Z.store.measure d).D (reference G d) else 0 := by
  let data := H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  have issued := Jury.enrolled ν M Z.scheme Z.criterion σ hG data.Taylor data.still data.base (d:=d)
  have unchanged : substitute (X:Cn) (Reg.Faith.reports ν Z.criterion M d) =
      Reg.Faith.reports ν Z.criterion M d :=
    Jury.peer _ _ (issued.glance X).exact (by rw [Facets.team_one]; exact issued.exact)
  have root : Rooted (X:Cn) := by simp [Rooted]
  have real : Reg.Unique.CoreR (X:Cn) := by simp [Reg.Unique.CoreR]
  have placed := Jury.solved ν M Z.scheme Z.criterion σ hG data.Taylor data.still data.base (d:=d) root real
  rw [unchanged] at placed
  simpa only [deck0,Normalize.author] using placed k

theorem realSum (d q : ℕ) (g : ℝ) : forecast Z M ν d q g =
    ∑ k ∈ range (q+1), g^k • Reg.Faith.reports ν Z.criterion M d k := by
  ext1 n
  ext1 t
  ext1 p
  rw [WilsonPositionProgramTrialPublicJointPivotForecast.value]
  simp only [Finset.sum_apply,Pi.smul_apply,LinearMap.sum_apply,_root_.sum_apply,
    LinearMap.smul_apply,_root_.smul_apply,Complex.real_smul,Complex.ofReal_pow]

include H in
theorem bank (d q : ℕ) (g : ℝ) :
    Fray.SetEq (Z.store.measure d) 0 (forecast Z M ν d q g) := by
  rw [Fray.SetEq,stand0,Screen.recruit_one,realSum,_root_.map_sum]
  simp_rw [map_smul,coefficient Z M H ν d]
  simp [smul_ite]

include H in
theorem original {ι : Type*} (u : Filter ι) (d q : ℕ) (g : ι → ℝ) (small : Tendsto g u (𝓝 0)) :
    ∀ᶠ i in u, (Z.store.survey d).firstPass (Z.store.prepared d) (forecast Z M ν d q (g i)) = 0 := by
  have warm := WilsonPositionProgramTrialPublicJointPivotForecast.original Z M H ν u d q g small
  have zero : Tendsto (fun _:ι => guide G d (0:Change G d)) u (𝓝 0) := by simpa only [map_zero] using (tendsto_const_nhds (x:=(0:MoveSpace G d)))
  filter_upwards [(Z.store.survey d).unmoor (Z.store.prepared d) warm (fun _=>0) zero] with i same
  exact same.mp (bank Z M H ν d q (g i))

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotPrepositioned
