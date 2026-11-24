import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Affine
import YM.Next.RANK.Stretch

/-!
# Linear (not volume) fusion support price.

This crude bound, not sharp in `B`, will buy the missing shells between
capture levels of a path satisfying Tabs, without changing the path.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Lattice Corona Next.Rank.Thirst AnalyticNext.ConnectedActivity.Aff

lemma stop_mem_orbit {n : Side} (x : Site n) (w : Walk) : stop x w ∈ orbit x w := by
  induction w generalizing x with
  | nil => simp [orbit,visits,stop]
  | cons d w ih =>
    simp only [stop,orbit, visits, List.toFinset_cons]
    exact Finset.mem_insert_of_mem (ih (x + d.vec))

/-- Families with sparse radius ratios can pay linear path cost instead of
an enclosing box. No convexity or nonwrapping assumed. -/
lemma pair_cover {n : Side} (x y : Site n) {B : ℕ} (hB : 1 ≤ B) :
    coverNumber B {x, y} ≤ 4 * separation x y + 1 := by
  let w := corner x y
  refine le_trans (encumber _ _ hB _) (le_trans ((cover_mono ?sub _).trans (orbit_bill x w)) ?_)
  · exact Finset.insert_subset (orbit_start x w) (Finset.singleton_subset_iff.mpr (finish x y ▸ stop_mem_orbit x (corner x y)))
  exact Nat.add_le_add_right (path_length x y) _
end YM.Frontier6
