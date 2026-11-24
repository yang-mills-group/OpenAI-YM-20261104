import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6OfficialEmpty
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6EmptyForest
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
open Position Position.Axes
theorem blank {W : Type} [LinearOrder W] (F : Finset W → ℕ → ℂ) :
    bouquet F (∅ : Finset W) = Trunk.unit := by
  let empty : Finset W → ℕ → ℂ := 0
  have same : bouquet F (∅ : Finset W) = bouquet empty ∅ := by
    change (∑ k ∈ Finset.range 1, (Trunk.stack (marked W)).wages F k) ∅ =
      (∑ k ∈ Finset.range 1, (Trunk.stack (marked W)).wages empty k) ∅
    rw [Finset.sum_range_one,Finset.sum_range_one]
    rfl
  exact same.trans (Stencil.simple_E Trunk empty (marked W) (by rfl))

theorem forest {G : Gauge} {O : Land.Booked (Press.portDeck G)} (A : MS_Data G O)
    (μ : ℝ) (n j : ℕ) (u : Fin n → Label (Press.portDeck G)) (x : Points n) :
    Landing.moondye μ A u ∅ j x = if j=0 then 1 else 0 := by
  unfold Landing.moondye MS.Dial.tour
  exact (congr_fun (blank (MS.Dial.book A u μ _)) j).trans (WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6OfficialEmpty.heat j)

theorem original {G : Gauge} (Z : WilsonPrescription G) {simple : G.Simple}
    {σ : Prescription (Press.portDeck G)} {dial : Bool}
    (matched : Main.Match Z simple (WilsonCapturedPhysicalMSDatum.original G) σ dial)
    (μ : ℝ) (n j : ℕ) (u : Fin n → Label (Press.portDeck G)) (x : Points n)
    (m : XSpace.Mesh) (even : Even m.p.side.val) (place : Fin n → Cover) (anchor : Cover) (η : ℝ) :
    let row := Top.value Z.scheme u σ anchor place m.p.side η (∅ : Finset (Fin n))
    PhysicalSum G σ.team η m.p.side true (∅ : Finset (Fin n)) place anchor
      (ApplyMF (Press.wickInput Z.scheme) (Stripped σ.team) σ u) row ∧
    row j = Landing.moondye μ (WilsonCapturedPhysicalMSDatum.original G) u ∅ j x ∧ row = Trunk.unit := by
  intro row
  have paid := matched.exactAtCutoff m.p.side even (∅ : Finset (Fin n)) place anchor η u
  have receipt := WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6OfficialEmpty.vacant σ.team η m.p.side true place anchor _ row paid
  exact ⟨paid,(congr_fun receipt j).trans ((WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6OfficialEmpty.heat j).trans
    (forest (WilsonCapturedPhysicalMSDatum.original G) μ n j u x).symm),receipt⟩
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6EmptyForest
