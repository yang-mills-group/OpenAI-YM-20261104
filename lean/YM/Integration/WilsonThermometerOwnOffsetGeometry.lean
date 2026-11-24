import YM.Integration.WilsonThermometerOwnOffsetJoint
import YM.Integration.WilsonThermometerOwnOffsetRadii
import YM.OPE.Samples.Layout

/-! Real displaced descendants preserve the separated detector geometry across
all intervening Wilson meshes, including opposite reflected child residues. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOwnOffsetGeometry
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetJoint
open scoped Classical Topology
variable {G : Gauge} (R : Run G) {N p k : ℕ} {I : Type} [Fintype I] [DecidableEq I]
variable (simple : G.Simple) (z : I → Site (R.family.side N p)) (t : ℕ) (names : Census I)
local notation "A" => R.alloy.B.a
local notation "B" => R.family.path.levels.budget
local notation "O" => origins R z
local notation "width" => (fun j (_ : I) => radius R t k j)

include simple in
theorem production : Brine R.family.path k (renal A) (near A) := by
  have h := (R.again simple).1.scrim.costs.stay
  exact ⟨fun i _=>h.water i (Nat.zero_le _),fun i _=>h.mint i (Nat.zero_le _),
    fun i _=>h.split i (Nat.zero_le _),fun i _=>h.support i (Nat.zero_le _)⟩

omit [Fintype I] [DecidableEq I] in
theorem placed {j : ℕ} (hj:k≤j) (hn:j≤N) (i:I) :
    (R.family.S.toDepth hj p).parent (O j i)=O k i := by
  unfold origins WilsonThermometerOwnOffsetNectar.location;rw [dif_pos hn,dif_pos (hj.trans hn)]
  exact (Next.Rank.Station.parent_nested (R.family.S.toDepth hj p) (R.family.S.toDepth hn p)
    (R.family.S.toDepth (hj.trans hn) p) (R.family.S.toDepth_odd hj p)
    (R.family.S.toDepth_odd hn p) (z i)).symm

omit [Fintype I] [DecidableEq I] in
theorem parent {j : ℕ} (hn:j<N) (i:I) :
    (R.family.path.levels.clock.op j p).ratio.parent (O (j+1) i)=O j i := by
  unfold origins WilsonThermometerOwnOffsetNectar.location;rw [dif_pos (show j+1≤N from hn),dif_pos hn.le]
  exact (Next.Rank.Station.parent_nested _ (R.family.S.toDepth hn p) _ (R.family.S.block_odd _)
    (R.family.S.toDepth_odd hn p) (z i)).symm

include simple
omit [Fintype I] [DecidableEq I] in
theorem retained (room : ∀ i i' : I,i≠i' → (B k).B^2 < separation (O k i) (O k i'))
    {j : ℕ} (hj:k≤j) (hn:j≤N) (i i' : I) (ne:i≠i') :
    (B j).B^2 < separation (O j i) (O j i') := by
  let X := R.family.S.toDepth hj p
  have spread := (OPE.Log.Trunk.Canvas.expands (C:=R.family) (O j i) (O j i') hj).1
  rw [placed R z hj hn i,placed R z hj hn i'] at spread
  have scaled := Nat.mul_le_mul_left X.count.val (room i i' ne)
  rw [Nat.mul_succ] at scaled
  have extent := Ribbons.gap_comp R.family p k j (production R simple) hj
  exact Nat.lt_of_le_of_lt extent (Nat.lt_of_add_lt_add_right (scaled.trans_lt spread))

theorem admitted (room : ∀ i i' : I,i≠i' → (B k).B^2 < separation (O k i) (O k i')) :
    Matchup R.family.path (mutt A R.Q) (renal A) p N k O width names := by
  let h := production (k:=k) R simple
  have ramp (j : ℕ) (hj:k≤j) (hn:j≤N) :=
    retained R simple z room hj hn
  have unique (j : ℕ) (hj:k≤j) (hn:j≤N) : Injective (O j) := by
    intro i i' same;by_contra ne
    have gap := ramp j hj hn i i' ne
    rw [same,separation_self] at gap;omega
  have scrim := (R.again simple).1.scrim
  refine ⟨fun j hj _ _=>radius_pos R t k j hj,
    fun j hj hn x=>(Occupancy.of_injective (unique j hj hn) x).trans (scrim.back j),
    fun j hj hn x=>(Occupancy.of_injective (unique (j+1) (hj.trans j.le_succ) hn) x).trans (scrim.back j),
    fun j _ hn=>funext (parent R z hn),?_⟩
  intro j hj hn
  have spaced : Drake names (B j).B (O j) := ⟨fun _ _ i _ i' _ ne=>(ramp j hj hn.le i i' ne).le⟩
  apply spaced.palms (v:=fun _=>renal A j*radius R t k (j+1)) _
    (fun _=>radius_pos R t k j hj)
    (fun _=>mul_pos (h.water j hj).2 (radius_pos R t k (j+1) (hj.trans j.le_succ))) (h.support j hj)
  intro _
  have fee := mul_le_mul_of_nonneg_right (h.mint j hj) (radius_pos R t k j hj).le
  rw [one_mul] at fee
  rw [radius_next R t k j hj]
  calc radius R t k j ≤ (renal _ j*near _ j*mintK (B j).B)*radius R t k j := fee
       _ = _ := by unfold near sap;ring

end YM.Integration.WilsonThermometerOwnOffsetGeometry
end
