import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6OfficialEmpty
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PostedEmpty
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
variable {G : Gauge}
variable (Z : WilsonPrescription G) {simple : G.Simple} {σ : Prescription (Press.portDeck G)} {dial : Bool}
    (matched : Main.Match Z simple (WilsonCapturedPhysicalMSDatum.original G) σ dial)
include matched in
theorem original (μ : ℝ) (d j : ℕ) (a : Sample 0) (even : Even a.F.p.side.val)
    (p : Tags G d 0) : Dframe.postedPoint μ Z.scheme σ d a j p = if j=0 then 1 else 0 := by
  let t : Fin 0 → Dframe.Toon G d := Fin.elim0
  let letters := Dframe.flash ∘ t
  have place : p = Dframe.fill t := Subsingleton.elim _ _
  have faced := Dframe.reads μ Z.scheme σ a t j
  have blank : (Finset.univ : Finset (Fin 0)) = ∅ := by simp
  rw [place,faced,blank]
  change Schedule.entries μ Z.scheme letters σ ∅ j a = _
  have unit : Top.value Z.scheme letters σ 0 a.layout a.F.p.side (μ-Schedule.theta a.F)
      (∅ : Finset (Fin 0)) = Trunk.unit :=
    (WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6OfficialEmpty.original Z matched a.F even a.layout 0
      (μ-Schedule.theta a.F) letters).2.1
  unfold Schedule.entries
  rw [unit]
  simp [MS.Vane.charge,WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6OfficialEmpty.heat]
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PostedEmpty
