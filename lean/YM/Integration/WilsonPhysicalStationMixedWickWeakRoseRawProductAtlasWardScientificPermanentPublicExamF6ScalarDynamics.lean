import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarSpines
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarArchive
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarDynamics
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
open Position Position.Axes

variable {G : Gauge} {W : Type} [LinearOrder W]
variable (A : MS_Data G (OpenAxis.Plot (Press.portDeck G))) (P : W → MS.Land.Plaid (Press.portDeck G) 0)
    (μ : ℝ) (x : W→QP) (injectiveX : Function.Injective x)
include injectiveX
theorem original (s : Finset W) (outside : s.card≠1) :
    MS.Dial.book A (WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarArchive.issued P) μ x s=0 := by
  let u := WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarArchive.issued P
  let R : W→Rake.Site G Unit := fun w=>Rake.rowM (MS.Tide.frameF Unit μ) A (u w)
  have pin := MS.Dial.pin A u μ injectiveX
  have bank : ∀w n i t,∃ c:ℂ,R w n i t=Koszul.coin c := by
    intro w n i t
    obtain ⟨amount,_,authentic⟩:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarArchive.row A P μ x injectiveX w
    have full : R w=Rake.circle (MS.Tide.frameF Unit μ).η (MS.Wind.col (Ace.estate G amount)) := (pin.2.1 w).symm.trans authentic
    rw [full]
    cases n with
    | zero => exact ⟨(amount:ℂ),rfl⟩
    | succ n => exact ⟨0,WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarSpines.vacancy⟩
  have identifies := Rake.perfect pin (WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarSpines.original R bank _ _ _ _ _)
  funext n
  change MS.Vane.blade (MS.Dial.spine A u μ x s n) ()=0
  rw [identifies,WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarSpines.absent R s outside]
  change limUnder atTop (fun _ : ℝ=>(0:ℂ))=0
  exact (tendsto_const_nhds : Tendsto (fun _ : ℝ=>(0:ℂ)) atTop (𝓝 0)).limUnder_eq
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarDynamics
