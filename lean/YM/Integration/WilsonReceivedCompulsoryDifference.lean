import YM.Integration.WilsonReceivedCompulsoryRate
import YM.Integration.WilsonReceivedCompulsoryCancellation
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Calculus

/-! The two physical hard programs share an ordered list before summing positions. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCompulsoryDifference
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


private theorem same_field {ι : Type} [DecidableEq ι] [Countable ι] (X : ι → Portrait P α)
    (anchor a d : α) (p : Sleet.Staff (brand X anchor) H) (weights : ι → ℝ)
    (Z : Set ι) (δ : ℝ)
    (values : ∀ F, Lyric.string (brand X d) H Chi.canonical p.1 p.2 F =
      Lyric.string (brand X a) H Chi.canonical p.1 p.2 F) :
    (Creek.theater H Chi.canonical X anchor weights Z δ).solvent d p =
    (Creek.theater H Chi.canonical X anchor weights Z δ).solvent a p := by
  have letters (v : α) := Creek.paper H Chi.canonical X anchor v weights Z δ p
  have stock := congrArg (fun m : Multiset ι => (m.map (sits Z weights δ)).prod)
    ((letters d).symm.trans (letters a))
  funext F
  exact congrArg₂ (· * ·) stock (values F)

private theorem inactive (P : BudgetPoint) (X : Support c) (v : Site c)
    (a d : Config G c → ℝ) (same : d = a) (b : ℝ) (positive : 0 ≤ b) :
    P.supBounds v X (d - a) b := by
  rw [same,sub_self]
  have zero := AnalyticBridge.VerifiedReset.Bill.const (G:=G) (n:=c) (o:=v)
    (Z:=fun _ => True) P (0 : ℝ)
  refine ⟨positive,fun F _ dirs hl hd => ?_⟩
  exact (zero.norm hl hd (show (fun _ : Config G c => True) F from trivial)).trans
    (by simpa only [norm_zero] using positive)

def atOrder (a d : α) (q : ℕ) : Prop :=
    ∃ f : word → ℝ, (∀ p, 0 ≤ f p) ∧
      (∀ p ∈ roster, ∀ x ∈ (table).halls p,
        P'.p.supBounds x ((table).halls p) ((table).solvent d p - (table).solvent a p) (f p)) ∧
      Ac.Hit (table).halls P'.p.B f (P'.p.supportExponent + 1 + 1) (2 * (gStep P.beta)^q)

include fits in
/-- After the original connected sum removes words missing the old hard
inventory, the complete difference costs twice one enrolled rooted price. -/
theorem original (a d : α)
    (equal_regular : ∀ j n, (M j).wing = Wing.logKey n → brand M a j = brand M d j)
    {q : ℕ} (enrolled : q ≤ eye.height) (weak : gStep P.beta ≤ 1) :
    atOrder (k:=k) (P':=P') H A r U positive slots t a d q := by
  have booked := WilsonReceivedCompulsoryRate.through (k:=k) (P':=P')
    H eye A r U positive slots fits t enrolled weak
  obtain ⟨f,price,held,rooted⟩ := booked.grants
  refine ⟨fun p => 2 * f p,fun p => mul_nonneg (by norm_num) (price p),?_,?_⟩
  · intro p hp x hx
    by_cases live : WilsonThermometerCompulsoryWords.used H A r U positive slots t p
    · have named := held p ⟨hp,live⟩
      simpa only [two_mul] using AnalyticBridge.VerifiedReset.sup_sub (named.1.angle d)
        (named.1.angle a) (named.2 d x hx) (named.2 a x hx)
    · have agree (F : Config G c) :
          Lyric.string (brand M a) H Chi.canonical p.1 p.2 F =
          Lyric.string (brand M d) H Chi.canonical p.1 p.2 F := by
        by_cases clear : ∀ s, Matter.own (p.1.2 s).val = ∅
        · exact WilsonReceivedCompulsoryCancellation.word H M Chi.canonical a d equal_regular p F clear
        · push Not at clear
          obtain ⟨s,hs⟩ := clear
          have absent (v : α) : Lyric.string (brand M v) H Chi.canonical p.1 p.2 F = 0 := by
            by_contra h
            exact live ⟨⟨v,F,h⟩,s,hs⟩
          rw [absent a,absent d]
      exact inactive _ _ _ _ _
        (same_field H M t a d p l marks 0 (fun F => (agree F).symm))
        _ (mul_nonneg (by norm_num) (price p))
  · intro x
    have twice := budget_scale (by norm_num : (0:ℝ) ≤ 2) (rooted x)
    refine budget_mono twice (fun p => ?_) (fun p => ?_)
    · split
      · exact mul_nonneg (mul_nonneg (by norm_num) (price p)) (Real.exp_pos _).le
      · exact le_rfl
    · split <;> simp [*,mul_assoc]
end YM.Integration.WilsonReceivedCompulsoryDifference
end
