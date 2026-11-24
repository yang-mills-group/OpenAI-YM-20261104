import YM.OPE.Compatible.Dale.Fronds
/-!
# Horizontal+vertical available
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory
open scoped Topology BigOperators ComplexConjugate Classical
variable {n c f:Side} (g:Ratio c f) (hp:Even c.val)(he:Odd g.count.val)
open Score Stand
local notation "μ" => even_both g hp
local notation "X" => forest g he
abbrev stageScore := (Pond μ).tie (Pond hp) (LiftV g hp)
abbrev berth := LiftV g hp '' ({origin hp}: Set _)
abbrev Stitched:= (stageScore g hp).Stand (berth g hp)
@[simp] lemma berths : berth g hp=({origin μ}: Set _):=by simp [berth,origin_step]
abbrev standWith (T: Plot hp): Stitched g hp:= T.tieIn (vforest g hp he) (travel_v g hp he) (hike_same g hp he) (4*g.count.val+1) fun i=> Nat.lt_succ_of_le ((forest g he).bound i.val)
lemma spinD (T:Plot hp)(x:Limb μ): (standWith g hp he T).Branch (Sum.inl x) ↔ x.val ∈ (forest g he).trunks:= (Stand.coversD ..).trans (branch_rep g hp he)
lemma spinW (T:Plot hp)(x:Limb hp): (standWith g hp he T).Branch (Sum.inr x) ↔ T.Branch x:= Stand.coversW ..
-- avoid flag transport on Stand; generic recouple with roots equal
end YM.OPE.Cascade
