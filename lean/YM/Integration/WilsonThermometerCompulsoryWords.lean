import YM.QuadraticLocal.Travel
import YM.RemainderComparison.Creek.Icing

/-! The original connected-word price for a nonempty old compulsory inventory. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerCompulsoryWords
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves Merge Palette Next.Scheduling
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Mosaic RemainderComparison.Muse
open RemainderComparison.Sleet RemainderComparison.Serif RemainderComparison.Typeface RemainderComparison.Flues
open Marker Mallow Ovens Progress.DirectedRecipe QuadraticLocal QuadraticLocal.Travel QuadraticLocal.Trigger
open RemainderComparison.WickReps
open scoped Topology BigOperators Classical

variable {G : Gauge} {n c L : Side} {S : StepData c n} {C : Teller G}
    {D : Tube G S} {P : Rep G n} {P' : Rep G c} {w x κ z e Y Γ K b b' : ℝ}
    {Q : ConnectedActivityE6.Target G C} {h : ConnectedActivityE6.Target.Order G w}
    {V I : Type} {α : Type} [DecidableEq V] [Countable I] {R : Marker.Census V}
    {o : V → Site n} {k : ℕ}

variable (H : Cash w x κ L Q h z D P) (eye : Travel.Eyes H P' e Γ Y K k)
    (A : Gallery α I o P R) (r : V → ℝ) (U : Travel.Seal A r b b')
    (positive : ∀ v, 0 < r v) (slots : HasSlots P.p P.activities)
    (fits : 2*(b+b') ≤ K) (t : α)
local notation "M" => Trigger.listCosts A r positive slots U.supE U.crown (Travel.sighting A r U) U.looks
local notation "marks" => (Set.univ : Set (Trigger.Table A × Bool))
local notation "l" => (fun _ : Trigger.Table A × Bool => (1:ℝ))
local notation "actor" => (brand M t)
local notation "table" => Creek.theater H Chi.canonical M t l marks 0
local notation "roster" => Creek.Academy H Chi.canonical M t l marks 0 k
local notation "word" => Sleet.Staff actor H

/-- A genuine unmarked or marked old hard key participates in a living term. The
field and the tests are part of the original countable connected-word expansion. -/
def used (p : word) : Prop :=
  (∃ (a : α) (F : Config G c), Lyric.string (brand M a) H Chi.canonical p.1 p.2 F ≠ 0) ∧
    ∃ s, (Matter.own (p.1.2 s).val).Nonempty

include fits in
/-- Every ordered connected word with a live original compulsory owner is
summed at its rooted full moving-field derivative price. -/
theorem paid : Manor.Spinal table
    {p : word | p ∈ roster ∧ used H A r U positive slots t p}
    (Flues.candle M t S) P'.p (P'.p.supportExponent+1+1) ((gStep P.beta)^eye.height) := by
  let fiscal := Travel.fiscal H eye A r U positive slots fits t
  let subset := {p : word | Muse.Pure actor H Chi.canonical marks k p ∧ Sleet.Flurry H p.1 k eye.height}
  have high : Manor.Spinal table subset (Flues.candle M t S) P'.p
      (P'.p.supportExponent+1+1) ((gStep P.beta)^eye.height) :=
    Creek.prior H Chi.canonical M t l marks 0 P'.p (fun a =>
      (Typeface.ally H Chi.canonical eye.pad M t a l marks 0 eye.bells fiscal P'.p
        eye.block eye.pole le_rfl le_rfl).2.1)
  apply high.skim _ le_rfl le_rfl
  rintro p ⟨enrolled,⟨⟨a,F,active⟩,s,i,hi⟩⟩
  refine ⟨⟨?_,enrolled.1⟩,?_⟩
  · simp [Muse.virgin,Mosaic.Verse.load]
  · by_contra cold
    have no := (Lyric.listens (brand M a) H Chi.canonical p.1 p.2 F active
      (fun heat => cold (Or.imp_right (Or.imp_right (fun h => (Sleet.within x L).trans h)) heat))).no_packet s
    simp only [no.2.2.2,Finset.notMem_empty] at hi

end YM.Integration.WilsonThermometerCompulsoryWords
end
