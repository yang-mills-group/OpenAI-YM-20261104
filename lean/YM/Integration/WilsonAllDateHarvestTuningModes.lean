import YM.RG05Readout.Many.Run

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestTuningModes
open Lattice Marker Extra.Histories RG05Readout.Many
open scoped Classical

variable {G : Gauge} {C : Family G} {n m j per : ℕ}
variable {W : Type} [Fintype W] [DecidableEq W]
variable (o : W → Site (C.side n per)) (E : W → Motion) (roster : Census W) (nm : n ≤ m)

private theorem sheltered (mj : m ≤ j) (u : Finset (ManyStem C o j))
    (enrolled : u ∈ (Mine.masts o E nm (barren o E roster m) j).choices) :
    Lit (barren o E roster m) (Mine.shelter o nm mj) u := by
  unfold Mine.masts at enrolled
  rw [dif_pos mj] at enrolled
  exact (Finset.mem_filter.mp enrolled).2

/-- Every occupied high-interval mode uses each of its original colors at most once. -/
theorem cardinal (mj : m ≤ j)
    (s : (Mine.masts o E nm (barren o E roster m) j).Mode) :
    s.val.card ≤ Fintype.card W := by
  have down := sheltered o E roster nm mj s.val s.property
  have colors : Lit roster ((Mine.tree o E).labelY m) down.climb.val :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp down.climb.property).1).2
  exact down.keep_count.symm.le.trans
    (colors.keep_count.symm.le.trans (Finset.card_le_univ colors.climb.val))

/-- At the tuning date the shelter is the identity, so the original ban
applies to every distinct pair of occupied physical anchors. -/
theorem separated :
    Choices o E m (Mine.masts o E nm (barren o E roster m) m) := by
  intro s h i hi j hj hij
  have down := sheltered o E roster nm (le_refl m) s.val s.property
  have original := barraged o E roster down.climb (down.keep_count.symm ▸ h)
    (Mine.shelter o nm le_rfl i) (Finset.mem_image_of_mem _ hi)
    (Mine.shelter o nm le_rfl j) (Finset.mem_image_of_mem _ hj)
    (fun same => hij (down.2 hi hj same))
  simpa only [Mine.vanishDepth] using original

theorem pair (s : (Mine.masts o E nm (barren o E roster m) m).Mode)
    (h : 2 ≤ s.val.card) :
    ∃ a ∈ s.val, ∃ b ∈ s.val, a ≠ b ∧
      (Mine.tree o E).supportX m a ≠ (Mine.tree o E).supportX m b ∧
      (C.path.levels.budget m).B ^ 2 + 1 ≤
        separation ((Mine.tree o E).supportX m a) ((Mine.tree o E).supportX m b) := by
  obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.mp h
  have dist := separated o E roster nm s h a ha b hb hne
  refine ⟨a, ha, b, hb, hne, ?_, dist⟩
  intro coincident
  rw [coincident, separation_self] at dist
  omega

end YM.Integration.WilsonAllDateHarvestTuningModes
