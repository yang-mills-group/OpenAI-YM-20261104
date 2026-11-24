import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6EmptyForest
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PostedEmpty
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6EmptyWave
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
theorem raw {G : Gauge} {O : Booked (Press.portDeck G)} (A : MS_Data G O)
    (μ : ℝ) (h j : ℕ) (x : Stage 0) (p : Tags G h 0) :
    Equator.wave μ A h 0 x j p = if j=0 then 1 else 0 := by
  let t : Fin 0 → Dframe.Toon G h := Fin.elim0
  have placed : p = Dframe.fill t := Subsingleton.elim _ _
  change Dframe.meteor μ A h x.val j p = _
  rw [placed,Dframe.ribbon]
  change Landing.moondye μ A (Dframe.flash ∘ t) Finset.univ j x.val = _
  have vacant : (Finset.univ : Finset (Fin 0)) = ∅ := by simp
  rw [vacant]
  exact WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6EmptyForest.forest A μ 0 j (Dframe.flash ∘ t) x.val

theorem original {G : Gauge} (Z : WilsonPrescription G) {simple : G.Simple}
    {σ : Prescription (Press.portDeck G)} {dial : Bool}
    (matched : Main.Match Z simple (WilsonCapturedPhysicalMSDatum.original G) σ dial)
    (μ : ℝ) (h j : ℕ) (x : Stage 0) (s : Sample 0) (even : Even s.F.p.side.val)
    (p : Tags G h 0) :
    Dframe.postedPoint μ Z.scheme σ h s j p = Equator.wave μ (WilsonCapturedPhysicalMSDatum.original G) h 0 x j p ∧
      Equator.wave μ (WilsonCapturedPhysicalMSDatum.original G) h 0 x j p = if j=0 then 1 else 0 := by
  have held := raw (WilsonCapturedPhysicalMSDatum.original G) μ h j x p
  exact ⟨(WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PostedEmpty.original Z matched μ h j s even p).trans held.symm,held⟩
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6EmptyWave
