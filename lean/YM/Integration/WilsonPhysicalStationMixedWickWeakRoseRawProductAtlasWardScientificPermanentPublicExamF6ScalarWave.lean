import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarArchive
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6EmptyWave
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarWave
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
open Position Position.Axes
variable {G : Gauge}
theorem title (u : MS.Rake.Label (Press.portDeck G)) (zero : u.h=0) : ∃ P : MS.Land.Plaid (Press.portDeck G) 0, u=⟨0,P⟩ := by
  obtain ⟨j,P⟩ := u
  change j=0 at zero
  subst j
  exact ⟨P,rfl⟩
theorem original (A : MS_Data G (OpenAxis.Plot (Press.portDeck G))) (μ : ℝ) (h k : ℕ) (x : Stage 1) (t : Fin 1 → Dframe.Toon G h) (zero : ∀i,(t i).size=0) : Equator.wave μ A h 1 x (k+1) (Dframe.fill t)=0 := by
  change Dframe.meteor μ A h x.val (k+1) (Dframe.fill t)=0
  rw [Dframe.ribbon]
  let u := Dframe.flash ∘ t
  choose P paid using fun i => title (u i) (zero i)
  have own : u=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarArchive.issued P := funext paid
  change Landing.moondye μ A u Finset.univ (k+1) x.val=0
  have single : (Finset.univ : Finset (Fin 1))={0} := by ext i; fin_cases i; simp
  rw [own,single]
  exact WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarArchive.original A P μ _ (fun _ _ _=>Subsingleton.elim _ _) 0 k
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarWave
