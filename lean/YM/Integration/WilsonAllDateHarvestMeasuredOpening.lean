import YM.Integration.WilsonAllDateHarvestEndpointOpening
import YM.Integration.WilsonMixedTaggedFields

/-! The full physical field being reopened on the reporting day is the dated
ordinary Wilson push. Its dormant modes vanish throughout a single measured
history, including before division by the vacuum. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestMeasuredOpening

open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Next.Rank.Station
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage
open scoped BigOperators Classical

variable {G:Gauge} {C:Family G} {n m p N:ℕ} {W:Type} [DecidableEq W] [Fintype W]
variable (o:W→Site (C.side n p)) (E:W→Motion) (s:W→ℕ) (q:ManyStem C o n→Body)
variable (S:(j:W)→Emblems C (s j)) (x:(j:W)→Palette C (s j)) (roster:Census W)
variable (h:C.Makes)
set_option quotPrecheck false
local notation "A" => Mine.tree o E
local notation "Y" => C.path.rep N p
local notation "I" => headings o E q
local notation "H" => Mine.ward o E roster
local notation "v" => Launch (m:=m) s S x
local notation "cols" => WilsonMixedTaggedFields.columns o E s q S x m N
local notation "dark" => shadow A s I
local notation "field" => fun (i:ℕ) (iN:i ≤ N)=>
  gust C.path N p N (birth (H i) (Y N) (cols i)) i iN

/-- Original clearance and the physical lesson open both funded endpoints to
the full census on their actual signed Wilson field. -/
theorem original {D:Address.Rail C} {T:Pens C p W} {B:ℕ→ℕ→ℝ} {Q:ℕ→ℝ}
    {u:(j:W)→ℕ→Palette C (s j)} (nm:n ≤ m) (mN:m ≤ N)
    {X:∀i,Config G (C.side i p)→Poly (H i)}
    (history:Replay A s (le_refl n) N X N)
    (identified:∀i,n ≤ i→∀iN:i ≤ N,X i=field i iN ∧
      ∀U (a:(H i).Mode),¬Disjoint (dark i) (a.val:Set _)→(X i U).part a=0)
    (lesson:Lesson (D:=D) h s n N N p T B Q u) (clear:Clearance o E s I roster m)
    {L Z:Config G (C.side m p)→Poly (Mine.masts o E nm (barren o E roster m) m)}
    {w:ManyStem C o m→ℝ} {α ρ:ℝ} (positive:∀i,0 < w i)
    (low:MenuBoard (Y m) (imprint h A I T m mN) L ((A).supportX m) w α ρ)
    (high:MenuBoard (Y m) (imprint h A I T m mN) Z ((A).supportX m) w α ρ)
    (z:ℂ) (head:∀U,narrow (WilsonMixedTaggedSeparatedBoard.admitted o E roster nm (le_refl m))
      (field m mN U)=WilsonAllDateHarvestAffine.blend (L U) (Z U) z) :
    let inc:=WilsonMixedTaggedSeparatedBoard.admitted o E roster nm (le_refl m)
    let opened:=WilsonAllDateHarvestEndpointOpening.opening inc (dark m)
    ∃ F:∀i,Config G (C.side i p)→Poly (H i), Replay A s (le_refl n) m F N ∧
      (∀i,n ≤ i→∀iN:i ≤ N,F i=field i iN) ∧
      MenuBoard (Y m) (imprint h A I T m mN) (fun U=>opened (L U)) ((A).supportX m) w α ρ ∧
      MenuBoard (Y m) (imprint h A I T m mN) (fun U=>opened (Z U)) ((A).supportX m) w α ρ ∧
      F m=fun U=>WilsonAllDateHarvestAffine.blend (opened (L U)) (opened (Z U)) z := by
  have gate:=masts_block o E s I nm roster clear
  have dormant (i:ManyStem C o m) (hh:i∈dark m) :
      (imprint h A I T m mN i).2.1=0 ∧
      profile (Y m).activities (imprint h A I T m mN i).2.2=0 := by
    rw [lesson.cold A s I h mN nm i hh]
    refine ⟨rfl,?_⟩
    ext
    simp [profile,cram]
  have lower:Replay A s (le_refl n) m X N:=
    ⟨fun i ni im=>history.downhill i ni (im.trans_le mN)⟩
  refine ⟨X,lower,fun i ni iN=>(identified i ni iN).1,
    WilsonAllDateHarvestEndpointOpening.paid _ _ gate dormant positive low,
    WilsonAllDateHarvestEndpointOpening.paid _ _ gate dormant positive high,?_⟩
  exact WilsonAllDateHarvestEndpointOpening.intermediate _ _ gate (X m) (identified m nm mN).2 z
    (fun U=>by rw [(identified m nm mN).1];exact head U)

end YM.Integration.WilsonAllDateHarvestMeasuredOpening
