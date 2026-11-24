import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedMoments
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6EmptyForest
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedFilm
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
open Position Position.Axes

variable {G : Gauge} {W : Type} [LinearOrder W]
theorem film (A : MS_Data G (OpenAxis.Plot (Press.portDeck G))) (u : W→MS.Rake.Label (Press.portDeck G))
    (μ : ℝ) (x : W→QP) (separated : Function.Injective x) (w : W) (P : MS.Land.Plaid (Press.portDeck G) 0)
    (source : u w=⟨0,P⟩) (c : ℝ) (physical : MS.Theater.film (Press.portDeck G) P.2 (h:=0)=MvPolynomial.C (c:ℂ)) :
    MS.Dial.book A u μ x {w} 0 = (c:ℂ) := by
  have pin:=MS.Dial.pin A u μ separated
  have full : MS.Dial.spine A u μ x {w}=Rake.circle (MS.Tide.frameF Unit μ).η (MS.Wind.col (Ace.estate G c)) := by
    rw [pin.2.1 w]
    change Rake.rowM (MS.Tide.frameF Unit μ) A (u w)=_
    rw [source]
    unfold Rake.rowM
    exact congrArg (Rake.circle (MS.Tide.frameF Unit μ).η) (Ace.title A P c physical).symm
  change MS.Vane.blade (MS.Dial.spine A u μ x {w} 0) ()=_
  rw [full]
  change limUnder atTop (fun _:ℝ=>(c:ℂ))=(c:ℂ)
  exact (tendsto_const_nhds : Tendsto (fun _:ℝ=>(c:ℂ)) atTop (𝓝 (c:ℂ))).limUnder_eq
theorem original (A : MS_Data G (OpenAxis.Plot (Press.portDeck G))) (u : W→MS.Rake.Label (Press.portDeck G))
    (μ : ℝ) (x : W→QP) (separated : Function.Injective x) (w : W) (grade : (u w).h=0) :
    ∃P : MS.Land.Plaid (Press.portDeck G) 0,∃c : ℝ,u w=⟨0,P⟩ ∧
    MS.Theater.film (Press.portDeck G) P.2 (h:=0)=MvPolynomial.C (c:ℂ) ∧
    ∀ s : Finset W,w∉s→∀ k,MS.Dial.tour A u μ x (insert w s) k=(c:ℂ)*MS.Dial.tour A u μ x s k := by
  obtain ⟨P,source⟩:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarWave.title (u w) grade
  obtain ⟨c,physical⟩:=Ace.cost0 P
  refine ⟨P,c,source,physical,?_⟩
  let F:=MS.Dial.book A u μ x
  have held : ∀t:Finset W,w∈t→t.card≠1→F t=0 := fun t present many=>WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6InsertedBook.original A u μ x separated w grade t present many
  have single : bouquet F {w}=F {w} := by
    have own:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6OneBouquet.original Trunk (fun _ _ _=>Submodule.mem_top) (∅:Finset W) w (Finset.notMem_empty w) held
    change bouquet F (insert w (∅:Finset W))=Trunk.core (F {w}) (bouquet F ∅) at own
    simpa only [Finset.insert_empty,WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6EmptyForest.blank,Trunk.identityR] using own
  have empty : MS.Dial.tour A u μ x ∅ 0=1 := by
    change bouquet F ∅ 0=1
    rw [WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6EmptyForest.blank]
    exact (WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6OfficialEmpty.heat 0).trans (if_pos rfl)
  obtain ⟨a,paid⟩:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedMoments.original A u μ x separated w grade
  have amount := paid ∅ (Finset.notMem_empty w) 0
  simp only [Finset.insert_empty,empty,mul_one] at amount
  have identified : (a:ℂ)=(c:ℂ) := amount.symm.trans ((congrFun single 0).trans (film A u μ x separated w P source c physical))
  intro s outside k
  rw [paid s outside k,identified]
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedFilm
