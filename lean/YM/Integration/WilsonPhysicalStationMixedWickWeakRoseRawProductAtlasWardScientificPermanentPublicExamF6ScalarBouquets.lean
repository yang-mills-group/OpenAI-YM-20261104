import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6EmptyForest
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarBouquets
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
open Position Position.Axes

theorem original {W : Type} [LinearOrder W] (F : Finset W → ℕ → ℂ)
    (single : ∀w k, F {w} (k+1)=0) (only : ∀s : Finset W,s.card≠1→F s=0) :
    ∀ s : Finset W,∀ k, bouquet F s (k+1)=0 := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro k
    rw [WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6EmptyForest.blank]
    exact WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6OfficialEmpty.heat (k+1)
  | @insert w s outside ih =>
    intro k
    rw [show bouquet F (insert w s)=Trunk.core (F {w}) (bouquet F s) from
      Stencil.cheers Trunk (fun _ _ _=>Submodule.mem_top) only s w outside]
    change (∑ a ∈ useN.pieces (k+1), F {w} a.1 * bouquet F s a.2)=0
    apply Finset.sum_eq_zero
    intro a member
    obtain ⟨i,j⟩ := a
    have count := useN.pays member
    change i+j=k+1 at count
    cases i with
    | zero =>
      have h : j=k+1 := by simpa using count
      rw [h,ih k,mul_zero]
    | succ i => rw [single w i,zero_mul]
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarBouquets
