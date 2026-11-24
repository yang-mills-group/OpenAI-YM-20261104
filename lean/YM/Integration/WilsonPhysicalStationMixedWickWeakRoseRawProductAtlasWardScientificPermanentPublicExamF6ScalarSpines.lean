import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarCrossing
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarArchive
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarSpines
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
open Position Position.Axes


open MeasureTheory MS.Plane.Flux
variable {G : Gauge} {I W : Type} [LinearOrder W]
def chosen (R : W→Rake.Site G I) (s : Finset W) : Rake.Site G I :=
  if hs:s.Nonempty then if s.card=1 then R (s.min' hs) else 0 else 0
theorem absent (R : W→Rake.Site G I) (s : Finset W) (h : s.card≠1) : chosen R s=0 := by
  by_cases hs:s.Nonempty <;> simp [chosen,hs,h]
theorem vacancy : (0 : Law G)=Koszul.coin 0 := by
  funext w
  cases w <;> rfl
theorem scalar (R : W→Rake.Site G I) (bank : ∀w n i t,∃ c:ℂ,R w n i t=Koszul.coin c)
    (s : Finset W) (n : ℕ) (i : I) (t : ℝ) : ∃c:ℂ,chosen R s n i t=Koszul.coin c := by
  by_cases h:s.card=1
  · obtain ⟨w,rfl⟩:=Finset.card_eq_one.mp h
    simpa [chosen] using bank w n i t
  · rw [absent R s h]
    exact ⟨0,vacancy⟩
theorem original (R : W→Rake.Site G I) (bank : ∀w n i t,∃ c:ℂ,R w n i t=Koszul.coin c)
    (x : Rake.Position W I) (m : I→Measure QP) (K L : Rake.Planet G I) (F : Rake.Site G I) :
    Rake.Fields x m K L F R (chosen R) := by
  classical
  refine ⟨by simp [chosen],fun w=>by simp [chosen],?_⟩
  intro s large n
  have retired := absent R s (show s.card≠1 by omega)
  have quiet : Rake.lonely K F 0 n=0 := by
    unfold Rake.lonely
    apply Finset.sum_eq_zero
    intro a _
    funext i t
    exact WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarCrossing.quiet (K i t) (F (n-a) i t)
  have crossed : ∀ (t : Finset W) (j : ℕ×ℕ), Rake.regionC m
      (Rake.rootX x t-Rake.rootX x s) L (chosen R t j.1) (chosen R (s\t) j.2)=0 := by
    intro t j
    funext i τ
    obtain ⟨c,hc⟩:=scalar R bank t j.1 i τ
    change Latch.Cabin ((Rake.rootX x t-Rake.rootX x s) i) (L i τ) (m i) (chosen R t j.1 i τ) (chosen R (s\t) j.2 i τ)=0
    rw [hc]
    exact WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarCrossing.current _ _ _ _ _
  rw [retired]
  unfold Rake.multi
  rw [quiet,zero_add,Finset.sum_eq_zero (fun t _=>Finset.sum_eq_zero (fun j _=>crossed t j))]
  exact WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarCrossing.original m L
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarSpines
