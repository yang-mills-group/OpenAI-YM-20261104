import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedDynamics
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarWave
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6InsertedBook
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
open Position Position.Axes

variable {G : Gauge} {W : Type} [LinearOrder W]
theorem original (A : MS_Data G (OpenAxis.Plot (Press.portDeck G))) (u : W→MS.Rake.Label (Press.portDeck G))
    (μ : ℝ) (x : W→QP) (separated : Function.Injective x) (w : W) (grade : (u w).h=0)
    (s : Finset W) (present : w∈s) (many : s.card≠1) : MS.Dial.book A u μ x s=0 := by
  obtain ⟨P,source⟩:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarWave.title (u w) grade
  obtain ⟨amount,physical⟩:=Ace.cost0 P
  have pin:=MS.Dial.pin A u μ separated
  have full : MS.Dial.spine A u μ x {w}=Rake.circle (MS.Tide.frameF Unit μ).η (MS.Wind.col (Ace.estate G amount)) := by
    rw [pin.2.1 w]
    change Rake.rowM (MS.Tide.frameF Unit μ) A (u w)=_
    rw [source]
    unfold Rake.rowM
    exact congrArg (Rake.circle (MS.Tide.frameF Unit μ).η) (Ace.title A P amount physical).symm
  have scalar : ∀n i τ, ∃c:ℂ,MS.Dial.spine A u μ x {w} n i τ=Koszul.coin c := by
    intro n i τ
    rw [full]
    cases n with
    | zero => exact ⟨(amount:ℂ),rfl⟩
    | succ n => exact ⟨0,WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarSpines.vacancy⟩
  have earned:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedDynamics.original pin w scalar s present many
  funext n
  change MS.Vane.blade (MS.Dial.spine A u μ x s n) ()=0
  rw [earned]
  change limUnder atTop (fun _ : ℝ=>(0:ℂ))=0
  exact (tendsto_const_nhds : Tendsto (fun _ : ℝ=>(0:ℂ)) atTop (𝓝 0)).limUnder_eq
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6InsertedBook
