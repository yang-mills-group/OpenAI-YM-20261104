import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedMoments
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarHomes
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedMeteor
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
open Position Position.Axes
variable {G : Gauge}
theorem original (A : MS_Data G (OpenAxis.Plot (Press.portDeck G))) (μ:ℝ)(h n:ℕ)(x:Stage n)
    (t : Fin n→Dframe.Toon G h) (w : Fin n) (grade:(t w).size=0) :
    ∃c:ℝ,∀k,Equator.wave μ A h n x k (Dframe.fill t) =
      (c:ℂ)*Landing.moondye μ A (Dframe.flash ∘ t) (Finset.univ.erase w) k x.val := by
  let u := Dframe.flash ∘ t
  obtain ⟨c,paid⟩:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedMoments.original A u μ (Arrival.Schedule.plot x.val) (Arrival.Schedule.track x.property) w grade
  refine ⟨c,?_⟩
  intro k
  change Dframe.meteor μ A h x.val k (Dframe.fill t)=_
  rw [Dframe.ribbon]
  change MS.Dial.tour A u μ (Arrival.Schedule.plot x.val) Finset.univ k=(c:ℂ)*MS.Dial.tour A u μ (Arrival.Schedule.plot x.val) (Finset.univ.erase w) k
  have earn := paid (Finset.univ.erase w) (Finset.notMem_erase w _) k
  simpa only [Finset.insert_erase (Finset.mem_univ w)] using earn
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedMeteor
