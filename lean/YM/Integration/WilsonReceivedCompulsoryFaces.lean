import YM.Integration.WilsonReceivedCompulsoryRate
import YM.Integration.WilsonFirstReceivedGalleryRegular
import YM.QuadraticLocal.Glow

/-! Measure the complete funded regular log arising from original hard words. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCompulsoryFaces
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

/-- The original linked, masked, complex-valued coefficient on the true held field. -/
def markedLog (a : α) (F : Config G c) : Poly R :=
  (table).basin P'.p occupiedWords marks (Trigger.axis A r) a F

theorem read {q : ℕ}
    (paid : WilsonReceivedCompulsoryRate.atOrder (k:=k) (P':=P') H A r U positive slots t q)
    (covers : ∀ s : R.Mode, s.val.card ≤ k) (width : 0 ≤ P'.p.supportExponent+1+1)
    (a : α) (F : Config G c) (s : R.Mode) (v : V) (hv : v ∈ s.val) :
    Poly.toll r s * ‖(markedLog (k:=k) (P':=P') H A r U positive slots t a F).part s‖ ≤ (gStep P.beta)^q := by
  have chorus := Trigger.choir A r positive k covers
  let roots := Flues.candle M t S
  let bulbs := Pane.printBulbs (S.ratio.parent ∘ o) table marks (Trigger.axis A r) occupiedWords roots paid
  have wage := Pane.lightsPaid (S.ratio.parent ∘ o) table marks (Trigger.axis A r) occupiedWords roots paid chorus
  have lit := Pane.lit (S.ratio.parent ∘ o) table marks (Trigger.axis A r) occupiedWords roots paid
    (fun j => Trigger.colorCosting A S r slots j P'.p) a F chorus width
  have occupied := WilsonFirstReceivedGalleryRegular.occupied (P:=P') bulbs wage width positive a F s v hv
  have nonquiet : s ≠ R.quiet := by
    intro same
    rw [same] at hv
    exact Finset.notMem_empty v hv
  rw [lit] at occupied
  have fresh (Y : Poly R) : (GridRenewal.Rain.fresh Y).part s = Y.part s := by
    change Y.part s - (Poly.send R.quiet _).part s = _
    rw [Poly.part_send,if_neg nonquiet,sub_zero]
  exact fresh _ ▸ occupied

theorem difference {q : ℕ}
    (paid : WilsonReceivedCompulsoryRate.atOrder (k:=k) (P':=P') H A r U positive slots t q)
    (covers : ∀ s : R.Mode, s.val.card ≤ k) (width : 0 ≤ P'.p.supportExponent+1+1)
    (a d : α) (F : Config G c) (s : R.Mode) (v : V) (hv : v ∈ s.val) (θ : ℝ) (positiveθ : 0 ≤ θ) :
    Poly.toll r s * ‖(θ : ℂ) * ((markedLog (k:=k) (P':=P') H A r U positive slots t d F).part s -
      (markedLog (k:=k) (P':=P') H A r U positive slots t a F).part s)‖ ≤ θ * (2 * (gStep P.beta)^q) := by
  let field := fun a : α => (markedLog (k:=k) (P':=P') H A r U positive slots t a F).part s
  have left := read H A r U positive slots t paid covers width d F s v hv
  have right := read H A r U positive slots t paid covers width a F s v hv
  change Poly.toll r s * ‖(θ:ℂ)*(field d-field a)‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg positiveθ,mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ positiveθ
  exact (mul_le_mul_of_nonneg_left (norm_sub_le (field d) (field a)) (Poly.worth positive s).le).trans
    (by rw [mul_add,two_mul]; exact add_le_add left right)

end YM.Integration.WilsonReceivedCompulsoryFaces
end
