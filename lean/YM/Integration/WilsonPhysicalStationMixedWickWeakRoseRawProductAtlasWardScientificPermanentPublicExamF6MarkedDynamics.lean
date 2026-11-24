import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarSpines
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarCrossing
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedDynamics
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
open Position Position.Axes

open MeasureTheory
variable {G : Gauge} {I W : Type} [LinearOrder W]
def trimmed (w : W) (X : Rake.Dance G I W) (s : Finset W) : Rake.Site G I :=
  if w∈s ∧ s.card≠1 then 0 else X s
theorem kept (w : W) (X : Rake.Dance G I W) (s : Finset W) (h : w∉s) : trimmed w X s=X s := by simp [trimmed,h]
theorem atMark (w : W) (X : Rake.Dance G I W)
    (scalar : ∀n i t,∃ c:ℂ,X {w} n i t=Koszul.coin c) (s : Finset W)
    (hw : w∈s) (n : ℕ) (i : I) (t : ℝ) : ∃c:ℂ,trimmed w X s n i t=Koszul.coin c := by
  by_cases h:s.card=1
  · obtain ⟨j,rfl⟩:=Finset.card_eq_one.mp h
    have e:w=j:=Finset.mem_singleton.mp hw
    subst j
    simpa [trimmed] using scalar n i t
  · rw [show trimmed w X s=0 by simp [trimmed,hw,h]]
    exact ⟨0,WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarSpines.vacancy⟩
theorem original {x : Rake.Position W I} {m : I→Measure QP} {K L : Rake.Planet G I} {F : Rake.Site G I}
    {R : W→Rake.Site G I} {X : Rake.Dance G I W} (paid : Rake.Fields x m K L F R X)
    (w : W) (scalar : ∀n i t,∃ c:ℂ,X {w} n i t=Koszul.coin c) (s : Finset W)
    (member : w∈s) (many : s.card≠1) : X s=0 := by
  classical
  have actual : Rake.Fields x m K L F R (trimmed w X) := by
    refine ⟨by simpa [trimmed] using paid.1,fun j=>by simpa [trimmed] using paid.2.1 j,?_⟩
    intro t large n
    by_cases contains:w∈t
    · have absent : trimmed w X t=0 := by simp [trimmed,contains,show t.card≠1 by omega]
      have calm : Rake.lonely K F 0 n=0 := by
        unfold Rake.lonely
        apply Finset.sum_eq_zero
        intro j _
        funext i τ
        exact WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarCrossing.quiet (K i τ) (F (n-j) i τ)
      rw [absent]
      unfold Rake.multi
      rw [calm,zero_add]
      have crossed : ∀p∈Rake.picks t,∀ j:ℕ×ℕ, Rake.regionC m (Rake.rootX x p-Rake.rootX x t) L
          (trimmed w X p j.1) (trimmed w X (t\p) j.2)=0 := by
        intro p _ j
        funext i τ
        change Latch.Cabin ((Rake.rootX x p-Rake.rootX x t) i) (L i τ) (m i) (trimmed w X p j.1 i τ) (trimmed w X (t\p) j.2 i τ)=0
        by_cases h:w∈p
        · obtain ⟨c,hc⟩:=atMark w X scalar p h j.1 i τ
          rw [hc]
          exact WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarCrossing.current _ _ _ _ _
        · obtain ⟨c,hc⟩:=atMark w X scalar (t\p) (Finset.mem_sdiff.mpr ⟨contains,h⟩) j.2 i τ
          rw [hc]
          exact WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarCrossing.partner _ _ _ _ _
      rw [Finset.sum_eq_zero (fun p hp=>Finset.sum_eq_zero (fun j _=>crossed p hp j))]
      exact WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarCrossing.original m L
    · rw [kept w X t contains]
      have same : Rake.multi m x K L F (X t) (trimmed w X) n t=Rake.multi m x K L F (X t) X n t := by
        unfold Rake.multi
        apply congrArg (fun z => Rake.lonely K F (X t) n + z)
        apply Finset.sum_congr rfl
        intro p hp
        have first : w∉p := fun h=>contains ((Rake.n_small hp).1.le h)
        have second : w∉t\p := fun h=>contains (Finset.mem_sdiff.mp h).1
        rw [kept w X p first,kept w X (t\p) second]
      rw [same]
      exact paid.2.2 t large n
  have agreement := Rake.perfect paid actual
  rw [congrFun agreement s]
  simp [trimmed,member,many]
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedDynamics
