import YM.Integration.WilsonThermometerCompulsoryWords

/-! An original ordered term on a common physical Cash is independent of a
change of the hard ingredients when its component has no compulsory owner. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCompulsoryCancellation
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


open PhysicalNext.Repeat.Lotus
variable {G : Gauge} {n c L : Side} {S : StepData c n} {C : Teller G}
    {D : Tube G S} {P : Rep G n} {w x κ z : ℝ} {Q : ConnectedActivityE6.Target G C}
    {h : ConnectedActivityE6.Target.Order G w} {ι α : Type}
variable (H : Cash w x κ L Q h z D P) (M : ι → Portrait P α) (χ : Chi) (a b : α)

private theorem regular_ticket (p : H.ThinP) (i : Lyric.Drums (brand M a) S) (V : Config G c)
    (clear : Matter.own p.val = ∅) (active : Lyric.toe (brand M a) H χ p i V ≠ 0) :
    ∀ j ∈ i.val, ∃ n, (M j).wing = Wing.logKey n := by
  intro j member
  cases ht : (M j).wing with
  | logKey n => exact ⟨n,rfl⟩
  | gasKey n =>
    have hit := (Lyric.lead (brand M a) H χ p i V active).2.2.1
      (show Palette.sign (brand M a) S j ∈ i.reach from Finset.mem_image_of_mem _ member)
    have head : Sum.inr (Sum.inl n) ∈ p.val := by
      simpa only [Palette.sign,Typeface.brand,ht,Wing.badge] using hit
    have old : n ∈ Matter.own p.val := by simpa only [Matter.own,Finset.mem_toLeft,Finset.mem_toRight] using head
    simp only [clear,Finset.notMem_empty] at old

variable (stable : ∀ j n, (M j).wing = Wing.logKey n → brand M a j = brand M b j)

include stable in
/-- The real conditional molecule, including its tree and Gaussian integral,
reads only the unchanged regular ingredients on an owner-free support. -/
theorem component (p : H.ThinP) (i : Lyric.Drums (brand M a) S) (V : Config G c)
    (clear : Matter.own p.val = ∅) :
    Lyric.toe (brand M a) H χ p i V = Lyric.toe (brand M b) H χ p i V := by
  by_cases ordinary : ∀ j ∈ i.val, ∃ n, (M j).wing = Wing.logKey n
  · have same : (team (brand M a) i).own = (team (brand M b) i).own := by
      exact Finset.image_congr (fun j hj => (ordinary j hj).elim (fun n hn => stable j n hn))
    have ext : ∀ U V : Team P, U.own=V.own → U=V := by
      rintro ⟨u,hu⟩ ⟨v,hv⟩ rfl
      rfl
    unfold Lyric.toe
    rw [ext _ _ same]
  · have vanishes (t : α) : Lyric.toe (brand M t) H χ p i V = 0 := by
      by_contra hot
      exact ordinary (regular_ticket H M χ t p i V clear hot)
    rw [vanishes a,vanishes b]

include stable in
/-- Cancellation holds before summing any positions, for the entire signed
ordered physical Ursell word on the same held field. -/
theorem word (p : Sleet.Staff (brand M a) H) (V : Config G c)
    (clear : ∀ s, Matter.own (p.1.2 s).val = ∅) :
    Lyric.string (brand M a) H χ p.1 p.2 V = Lyric.string (brand M b) H χ p.1 p.2 V := by
  unfold Lyric.string
  apply congrArg (fun v : ℝ => Lyric.cadence H p.1 * v)
  apply Finset.prod_congr rfl
  intro s _
  exact component H M χ a b stable (p.1.2 s) (p.2 s) V (clear s)

end YM.Integration.WilsonReceivedCompulsoryCancellation
end
