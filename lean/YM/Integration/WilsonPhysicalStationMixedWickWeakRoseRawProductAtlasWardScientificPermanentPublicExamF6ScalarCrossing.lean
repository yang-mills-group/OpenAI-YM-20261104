import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6EmptyForest
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarCrossing
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
open Position Position.Axes

open MeasureTheory
open MS.Momentum MS.Heat MS.Tone MS.High MS.Plane.Flux MS.Rake
variable {G : Gauge}
theorem scatter0 {A : Type} (par : Sector A) (w : Legs A) :
    Koszul.scatter par w (fun _ _=> (0:ℂ))=0 := by
  induction w with
  | nil => rfl
  | cons i w ih => simpa only [Koszul.scatter_cons,mul_zero,zero_add] using ih
theorem current (a : ℂ) (x : QP) (K : Edge G) (μ : Measure QP) (H : Law G) :
    Latch.Cabin x K μ (Koszul.coin a) H=0 := by
  funext w
  unfold Latch.Cabin
  simp only [Latch.meshZ,Koszul.coin,mul_zero,zero_mul,integral_zero,Finset.sum_const_zero]
  exact scatter0 _ _
theorem partner (a : ℂ) (x : QP) (K : Edge G) (μ : Measure QP) (H : Law G) :
    Latch.Cabin x K μ H (Koszul.coin a)=0 := by
  funext w
  unfold Latch.Cabin
  simp only [Latch.meshZ,Koszul.coin,mul_zero,integral_zero,Finset.sum_const_zero]
  exact scatter0 _ _
theorem quiet (K : Edge G) (F : Law G) : tree parity K F 0=0 := by
  have zero : attaches parity K F 0 = (fun _ _=>0) := by
    funext l k
    simp [attaches]
  funext w
  rw [tree,zero]
  exact scatter0 _ _
theorem original {I : Type} (m : I → Measure QP) (K : Planet G I) : Trip (sailP m K) 0 0 := by
  rw [Trip,(retire K m).empty,add_zero]
  exact ⟨⟨0,fun _ _ _ _=>rfl⟩,fun _ _ _ _=>integrableOn_zero,Rake.river0.symm⟩
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarCrossing
