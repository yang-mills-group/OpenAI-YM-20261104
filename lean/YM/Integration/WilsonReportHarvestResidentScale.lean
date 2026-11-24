import YM.Integration.WilsonAllDateHarvestTuningModes
import YM.OPE.Samples.Layout

/-! The whole issued mixed roster inherits the actual dilation of its original admitting separation. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestResidentScale
open Lattice Marker Extra.Histories RG05Readout.Many
open scoped Classical
open private sheltered from YM.Integration.WilsonAllDateHarvestTuningModes
variable {G:Gauge} {C:Family G} {n m j per:ℕ}
variable {W:Type} [Fintype W] [DecidableEq W]
variable (o:W → Site (C.side n per))(E:W → Motion)(roster:Census W)(nm:n ≤ m)(mj:m ≤ j)
local notation "A"=>C.S.toDepth mj per
local notation "J"=>Mine.masts o E nm (barren o E roster m) j

/-- At any later date the exact mesh ratio multiplies the original admitted empty room. -/
theorem separated (s:(J).Mode)(h:2 ≤ s.val.card){a b:ManyStem C o j}
    (ha:a∈s.val)(hb:b∈s.val)(ne:a≠b):
    (A).count.val*(C.path.levels.budget m).B^2 <
      separation ((Mine.tree o E).supportX j a) ((Mine.tree o E).supportX j b):=by
  have down:=sheltered o E roster nm mj s.val s.property
  have old:=barraged o E roster down.climb (down.keep_count.symm ▸ h)
    (Mine.shelter o nm mj a) (Finset.mem_image_of_mem _ ha)
    (Mine.shelter o nm mj b) (Finset.mem_image_of_mem _ hb)
    (fun same=>ne (down.2 ha hb same))
  change (C.path.levels.budget m).B^2+1 ≤ 
    separation ((A).parent a.val.2) ((A).parent b.val.2) at old
  have scaled:=Nat.mul_le_mul_left (A).count.val old
  have actual:= (OPE.Log.Trunk.Canvas.expands (C:=C) a.val.2 b.val.2 mj).1
  change (A).count.val*separation ((A).parent a.val.2) ((A).parent b.val.2) <
    separation a.val.2 b.val.2 + (A).count.val at actual
  rw [Nat.mul_succ] at scaled
  exact Nat.lt_of_add_lt_add_right (scaled.trans_lt actual)

theorem pair (s:(J).Mode)(h:2 ≤ s.val.card):
    ∃a∈s.val,∃b∈s.val,(A).count.val*(C.path.levels.budget m).B^2 <
      separation ((Mine.tree o E).supportX j a) ((Mine.tree o E).supportX j b):=by
  obtain ⟨a,ha,b,hb,ne⟩:=Finset.one_lt_card.mp h
  exact ⟨a,ha,b,hb,separated o E roster nm mj s h ha hb ne⟩
end YM.Integration.WilsonReportHarvestResidentScale
