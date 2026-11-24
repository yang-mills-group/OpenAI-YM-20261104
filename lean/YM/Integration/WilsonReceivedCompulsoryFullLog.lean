import YM.Integration.WilsonReceivedCompulsoryRate
import YM.Integration.WilsonReceivedCompulsoryFaces
import YM.Integration.WilsonReceivedCompulsoryCancellation
import YM.Integration.WilsonFirstReceivedGalleryRegular
import YM.QuadraticLocal.Glow

/-! Identify the complete enrolled regular log difference before every required subword read. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCompulsoryFullLog
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


/-- The entire received regular log, with all words in its original Academy. -/
def fullLog (a : α) (F : Config G c) : Poly R :=
  (table).basin P'.p roster marks (Trigger.axis A r) a F

private theorem restricted {J : Type} {K L : Set J} (sub : L ⊆ K) (f g : J → Poly R)
    (hf : Summable (fun j : K => f j.val)) (hg : Summable (fun j : K => g j.val))
    (same : ∀ j ∈ K, j ∉ L → f j = g j) :
    (∑' j : K, f j.val) - (∑' j : K, g j.val) =
    (∑' j : L, f j.val) - (∑' j : L, g j.val) := by
  let inc : L → K := fun j => ⟨j.val,sub j.property⟩
  have hi : Function.Injective inc := by intro x y h; exact Subtype.ext (congrArg (fun j : K => j.val) h)
  have fl := hf.comp_injective hi
  have gl := hg.comp_injective hi
  change Summable (fun j : L => f j.val) at fl
  change Summable (fun j : L => g j.val) at gl
  rw [← hf.tsum_sub hg,← fl.tsum_sub gl]
  let z : J → Poly R := fun j => if j ∈ K then f j - g j else 0
  have active : Function.support z ⊆ L := by
    intro j hj
    by_contra not_live
    apply hj
    by_cases ht : j ∈ K
    · simp [z,ht,same j ht not_live]
    · simp [z,ht]
  calc
    (∑' j : K, (f j.val-g j.val)) = ∑' j : K, z j.val := tsum_congr (fun j => by simp [z,j.property])
    _ = ∑' j : J, z j := tsum_subtype_eq_of_support_subset (active.trans sub)
    _ = ∑' j : L, z j.val := (tsum_subtype_eq_of_support_subset active).symm
    _ = ∑' j : L, (f j.val-g j.val) := tsum_congr (fun j => by simp [z,sub j.property])

include eye fits in
/-- The full two-program signed log differs exactly by the selected old-owner
log. All unselected regular terms cancel at the common original field. -/
theorem original (a d : α)
    (same : ∀ j n, (M j).wing = Wing.logKey n → brand M a j = brand M d j)
    (covers : ∀ s : R.Mode, s.val.card ≤ k) (F : Config G c) :
    fullLog (k:=k) (P':=P') H A r U positive slots t d F -
      fullLog (k:=k) (P':=P') H A r U positive slots t a F =
    WilsonReceivedCompulsoryFaces.markedLog (k:=k) (P':=P') H A r U positive slots t d F -
      WilsonReceivedCompulsoryFaces.markedLog (k:=k) (P':=P') H A r U positive slots t a F := by
  let fiscal := Travel.fiscal H eye A r U positive slots fits t
  have full := Lanes.academy H Chi.canonical eye.pad M t l eye.bells fiscal P'.p eye.block eye.pole
    (le_refl _) (le_refl _)
  have chorus := Trigger.choir A r positive k covers
  have width : 0 ≤ P'.p.supportExponent+1+1 := by linarith [P'.p.exponent_pos]
  have sums (x : α) := Manor.standing x F marks (Trigger.axis A r) full.templary chorus width
  apply restricted (show occupiedWords ⊆ roster from fun _ hp => hp.1) _ _ (sums d) (sums a)
  intro p all outside
  have inactive : ¬ WilsonThermometerCompulsoryWords.used H A r U positive slots t p :=
    fun active => outside ⟨all,active⟩
  have string (B : Config G c) :
      Lyric.string (brand M d) H Chi.canonical p.1 p.2 B =
      Lyric.string (brand M a) H Chi.canonical p.1 p.2 B := by
    by_cases clear : ∀ s, Matter.own (p.1.2 s).val = ∅
    · exact (WilsonReceivedCompulsoryCancellation.word H M Chi.canonical a d same p B clear).symm
    · push Not at clear
      obtain ⟨s,hs⟩ := clear
      have zero (x : α) : Lyric.string (brand M x) H Chi.canonical p.1 p.2 B = 0 := by
        by_contra h
        exact inactive ⟨⟨x,B,h⟩,s,hs⟩
      rw [zero d,zero a]
  have letters (x : α) := Creek.paper H Chi.canonical M t x l marks 0 p
  have stock := congrArg (fun m : Multiset (Trigger.Table A × Bool) => (m.map (sits marks l 0)).prod)
    ((letters d).symm.trans (letters a))
  have equal : (table).solvent d p = (table).solvent a p := by
    funext F'
    exact congrArg₂ (· * ·) stock (string F')
  change (((table).wet P'.p d p F : ℝ) : ℂ) • _ = (((table).wet P'.p a p F : ℝ) : ℂ) • _
  simp only [Manor.wet,equal]

end YM.Integration.WilsonReceivedCompulsoryFullLog
end
