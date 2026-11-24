import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6FiledGraphArray
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6GraphCapReturn
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
open Position Position.Axes
variable {G : Gauge} {n c e : ℕ}
theorem original (μ : ℝ) (A : MS_Data G (OpenAxis.Plot (Press.portDeck G))) (x : Stage n) (k : ℕ)
    (d : Fin n→ℕ) (hc : ∀i,d i≤c) (he : ∀i,d i≤e) (v : ∀i,Sec G (d i)) :
    Equator.wave μ A c n x k (fun i=>up (hc i) (v i)) = Equator.wave μ A e n x k (fun i=>up (he i) (v i)) :=
  (Equator.wave_walk μ A (Nat.le_max_left c e) n x k (fun i=>up (hc i) (v i))).trans
    (Equator.wave_walk μ A (Nat.le_max_right c e) n x k (fun i=>up (he i) (v i))).symm
theorem sky (μ : ℝ) (A : MS_Data G (OpenAxis.Plot (Press.portDeck G))) (x : Stage n) (k : ℕ)
    (d : Fin n→ℕ) (hc : ∀i,d i≤c) (v : ∀i,Sec G (d i)) :
    Equator.wave μ A c n x k (fun i=>up (hc i) (v i)) = Equator.wave μ A (∑i,d i) n x k (fun i=>up
      (Finset.single_le_sum (f:=d) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)) (v i)) :=
  original μ A x k d hc _ v
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6GraphCapReturn
