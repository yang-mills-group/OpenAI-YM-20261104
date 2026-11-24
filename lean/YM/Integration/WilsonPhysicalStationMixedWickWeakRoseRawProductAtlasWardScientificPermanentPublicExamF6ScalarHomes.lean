import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarWave
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarRoster
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarHomes
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
open Position Position.Axes
variable {G : Gauge}
theorem basis (A : MS_Data G (OpenAxis.Plot (Press.portDeck G)))
    (μ : ℝ) (h n k : ℕ) (x : Stage n) (t : Fin n→Dframe.Toon G h)
    (zero : ∀i,(t i).size=0) : Equator.wave μ A h n x (k+1) (Dframe.fill t)=0 := by
  change Dframe.meteor μ A h x.val (k+1) (Dframe.fill t)=0
  rw [Dframe.ribbon]
  let u:=Dframe.flash ∘ t
  choose P paid using fun i=>WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarWave.title (u i) (zero i)
  have own : u=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarArchive.issued P := funext paid
  change Landing.moondye μ A u Finset.univ (k+1) x.val=0
  rw [own]
  exact WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarRoster.original A P μ _ (Arrival.Schedule.track x.property) _ k
theorem original (A : MS_Data G (OpenAxis.Plot (Press.portDeck G)))
    (μ : ℝ) (h n k : ℕ) (x : Stage n) (v : Tags G 0 n) :
    Equator.wave μ A h n x (k+1) (fun i=>up (Nat.zero_le h) (v i))=0 := by
  let M := (Dframe.meteor μ A h x.val (k+1)).compLinearMap
    (fun _ : Fin n => (up (Nat.zero_le h) : Sec G 0→ₗ[ℂ] Sec G h))
  change M v=0
  rw [Dframe.stencil_he M v]
  apply Finset.sum_eq_zero
  intro t _
  let lifted : Fin n→Dframe.Toon G h := fun i=>Dframe.enroll (Nat.zero_le h) (t i)
  have free : M (Dframe.fill t)=0 := by
    change Dframe.meteor μ A h x.val (k+1) (Dframe.fill lifted)=0
    exact basis A μ h n k x lifted (fun i=>Nat.eq_zero_of_le_zero (Dframe.size_le (t i)))
  rw [free,mul_zero]
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarHomes
