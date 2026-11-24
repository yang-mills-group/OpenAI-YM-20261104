import YM.Integration.WilsonReceivedCompulsoryDifference
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Local

/-! Restore the actual first-join distance factor on the complete signed rooted tally. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCompulsoryScaled
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



def atOrder (a d : α) (scale : ℝ) (q : ℕ) : Prop :=
  ∃ f : word → ℝ, (∀ p, 0 ≤ f p) ∧
    (∀ p ∈ roster, ∀ x ∈ (table).halls p,
      P'.p.supBounds x ((table).halls p) (scale • ((table).solvent d p - (table).solvent a p)) (f p)) ∧
    Ac.Hit (table).halls P'.p.B f (P'.p.supportExponent + 1 + 1) (scale * (2 * (gStep P.beta)^q))

theorem weighted (a d : α) {q : ℕ}
    (paid : WilsonReceivedCompulsoryDifference.atOrder (k:=k) (P':=P') H A r U positive slots t a d q)
    (scale : ℝ) (nonnegative : 0 ≤ scale) :
    atOrder (k:=k) (P':=P') H A r U positive slots t a d scale q := by
  obtain ⟨f,cost,paid,rooted⟩ := paid
  refine ⟨fun p => scale * f p,fun p => mul_nonneg nonnegative (cost p),?_,?_⟩
  · intro p hp x hx
    simpa only [abs_of_nonneg nonnegative] using
      AnalyticBridge.CouplingShape.sup_scale scale (paid p hp x hx)
  · intro x
    refine budget_mono (budget_scale nonnegative (rooted x)) (fun p => ?_) (fun p => ?_)
    · split
      · exact mul_nonneg (mul_nonneg nonnegative (cost p)) (Real.exp_pos _).le
      · exact le_rfl
    · split <;> simp [*,mul_assoc]
end YM.Integration.WilsonReceivedCompulsoryScaled
end
