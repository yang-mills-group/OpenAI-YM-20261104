import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedSingleton
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6InsertedBook
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6OneBouquet
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedMoments
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
open Position Position.Axes

variable {G : Gauge} {W : Type} [LinearOrder W]
theorem original (A : MS_Data G (OpenAxis.Plot (Press.portDeck G))) (u : W→MS.Rake.Label (Press.portDeck G))
    (μ : ℝ) (x : W→QP) (separated : Function.Injective x) (w : W) (grade : (u w).h=0) :
    ∃c:ℝ,∀s:Finset W,w∉s→∀k:ℕ, MS.Dial.tour A u μ x (insert w s) k=(c:ℂ)*MS.Dial.tour A u μ x s k := by
  obtain ⟨c,ground⟩:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedSingleton.original A u μ x separated w grade
  refine ⟨c,?_⟩
  intro s outside k
  let F := MS.Dial.book A u μ x
  have held : ∀t:Finset W,w∈t→t.card≠1→F t=0 := fun t present many=>WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6InsertedBook.original A u μ x separated w grade t present many
  have actual : bouquet F (insert w s)=Trunk.core (F {w}) (bouquet F s) :=
    WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6OneBouquet.original Trunk (fun _ _ _=>Submodule.mem_top) s w outside held
  change bouquet F (insert w s) k=(c:ℂ)*bouquet F s k
  rw [actual]
  change (∑a∈useN.pieces k,F {w} a.1*bouquet F s a.2)=(c:ℂ)*bouquet F s k
  have owns:(0,k)∈useN.pieces k := by
    simp [useN,SplitP.nat]
  rw [Finset.sum_eq_single_of_mem (0,k) owns]
  · change MS.Dial.book A u μ x {w} 0 * bouquet F s k=(c:ℂ)*bouquet F s k
    rw [ground 0,if_pos rfl]
  · intro a ha away
    obtain ⟨i,j⟩:=a
    have count := useN.pays ha
    change i+j=k at count
    have positive:i≠0 := by
      intro zero
      subst i
      have same:j=k:=by simpa using count
      exact away (by simp [same])
    change MS.Dial.book A u μ x {w} i * bouquet F s j=0
    rw [ground i,if_neg positive,zero_mul]
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedMoments
