import YM.Integration.WilsonReceivedCompulsoryFaces
import YM.QuadraticLocal.Tariff.Measure
import YM.Integration.WilsonFirstReceivedGalleryRegular
import YM.QuadraticLocal.Glow

/-! Measurability of the actual regular logarithm on the complete Wilson group. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCompulsoryMeasurable
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



local notation "occupiedWords" => {p : word | p ∈ roster ∧ WilsonThermometerCompulsoryWords.used H A r U positive slots t p}


/-- The actual signed occupied coefficient is measurable on every held Wilson field. -/
theorem original [Fintype V] {q : ℕ}
    (paid : WilsonReceivedCompulsoryRate.atOrder (k:=k) (P':=P') H A r U positive slots t q)
    (covers : ∀ s : R.Mode, s.val.card ≤ k) (width : 0 ≤ P'.p.supportExponent+1+1)
    (a : α) (s : R.Mode) (v : V) (hv : v ∈ s.val) :
    Measurable (fun F => (WilsonReceivedCompulsoryFaces.markedLog (k:=k) (P':=P')
      H A r U positive slots t a F).part s) := by
  have chorus := Trigger.choir A r positive k covers
  let roots := Flues.candle M t S
  let bulbs := Pane.printBulbs (S.ratio.parent ∘ o) table marks (Trigger.axis A r) occupiedWords roots paid
  haveI : Countable (Head S) := Refrain.countSeeds
  haveI : Countable word := by
    unfold Sleet.Staff
    haveI : Countable H.fragrances := by unfold Cash.fragrances; infer_instance
    infer_instance
  haveI : Countable (Pane.Table (R:=R) (S.ratio.parent ∘ o) table occupiedWords) := by
    unfold Pane.Table
    infer_instance
  have borel : Measurable (fun F => bulbs.log a F) := by
    apply Measurable.tsum
    intro j
    apply (Overlay.Bands.sends (bulbs.mode j)).measurable.comp
    unfold Lamps.light
    split
    · exact (bulbs.legal a j).borel
    · exact masked_measurable _ _ _ (bulbs.legal a j).borel
  have nonquiet : s ≠ R.quiet := by
    intro eq
    rw [eq] at hv
    exact Finset.notMem_empty v hv
  have eq : (fun F => (WilsonReceivedCompulsoryFaces.markedLog (k:=k) (P':=P') H A r U positive slots t a F).part s) =
      fun F => (bulbs.log a F).part s := by
    funext F
    rw [show bulbs.log a F = _ from Pane.lit (S.ratio.parent ∘ o) table marks (Trigger.axis A r) occupiedWords roots paid
      (fun j => Trigger.colorCosting A S r slots j P'.p) a F chorus width]
    change _ = _ - (Poly.send R.quiet _).part s
    rw [Poly.part_send,if_neg nonquiet,sub_zero]
    rfl
  rw [eq]
  exact (Poly.get s).continuous.measurable.comp borel

end YM.Integration.WilsonReceivedCompulsoryMeasurable
end
