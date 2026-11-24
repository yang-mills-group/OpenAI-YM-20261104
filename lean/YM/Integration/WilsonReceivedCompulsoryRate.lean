import YM.Integration.WilsonThermometerCompulsoryWords

/-! Read the original ordered connected-word price at any enrolled order. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCompulsoryRate
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


/-- All terms use the step geometry of the very same Cash. -/
def atOrder (q : ℕ) : Prop :=
  Manor.Spinal table
    {p : word | p ∈ roster ∧ WilsonThermometerCompulsoryWords.used H A r U positive slots t p}
    (Flues.candle M t S) P'.p (P'.p.supportExponent+1+1) ((gStep P.beta)^q)

include fits in
theorem through {q : ℕ} (enrolled : q ≤ eye.height) (weak : gStep P.beta ≤ 1) :
    atOrder (k:=k) (P':=P') H A r U positive slots t q := by
  have booked := WilsonThermometerCompulsoryWords.paid H eye A r U positive slots fits t
  unfold atOrder
  exact booked.skim (fun _ a => a) (pow_le_pow_of_le_one (inv_nonneg.mpr (Real.sqrt_nonneg _)) weak enrolled) le_rfl
end YM.Integration.WilsonReceivedCompulsoryRate
end
