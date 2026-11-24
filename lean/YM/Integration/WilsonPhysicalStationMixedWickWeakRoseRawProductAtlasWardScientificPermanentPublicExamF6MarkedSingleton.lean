import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarWave
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedSingleton
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
    ∃ c:ℝ, ∀ k,MS.Dial.book A u μ x {w} k=if k=0 then (c:ℂ) else 0 := by
  obtain ⟨P,source⟩:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarWave.title (u w) grade
  obtain ⟨amount,physical⟩:=Ace.cost0 P
  have pin:=MS.Dial.pin A u μ separated
  have full : MS.Dial.spine A u μ x {w}=Rake.circle (MS.Tide.frameF Unit μ).η (MS.Wind.col (Ace.estate G amount)) := by
    rw [pin.2.1 w]
    change Rake.rowM (MS.Tide.frameF Unit μ) A (u w)=_
    rw [source]
    unfold Rake.rowM
    exact congrArg (Rake.circle (MS.Tide.frameF Unit μ).η) (Ace.title A P amount physical).symm
  refine ⟨amount,?_⟩
  intro k
  cases k with
  | zero =>
    change MS.Vane.blade (MS.Dial.spine A u μ x {w} 0) ()=_
    rw [full,if_pos rfl]
    change limUnder atTop (fun _:ℝ=>(amount:ℂ))=(amount:ℂ)
    exact (tendsto_const_nhds : Tendsto (fun _:ℝ=>(amount:ℂ)) atTop (𝓝 (amount:ℂ))).limUnder_eq
  | succ k =>
    change MS.Vane.blade (MS.Dial.spine A u μ x {w} (k+1)) ()=_
    rw [full,if_neg (Nat.succ_ne_zero k)]
    change limUnder atTop (fun _:ℝ=>(0:ℂ))=0
    exact (tendsto_const_nhds : Tendsto (fun _:ℝ=>(0:ℂ)) atTop (𝓝 0)).limUnder_eq
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedSingleton
