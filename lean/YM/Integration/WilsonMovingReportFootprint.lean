import YM.RG16.Unmasked.Pace
import YM.Push.RELAY_DIFFERENCE.Stencils

/-! Fit any fixed actual signed stencil in the moving centered port uniformly
in every larger cutoff and every period. No equality of reporting grids. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingReportFootprint
open Filter Set Lattice RG RG16 RG16.Literal Cells Push.RelayDifference
open scoped Topology
variable {G : Gauge} (C : Family G) (hG : G.Simple)
include hG

theorem original (X : Finset Cover) {L B : ℝ} (hL : 0<L) (hB : 0<B) :
    ∀ᶠ k in atTop, ∀ N, k≤N → ∀ (p : ℕ) (hp : port C L B hL k≤N)
      (o : Site (C.side N p)), stamp X o ⊆ (center C.S p hp o).chamber 0 := by
  have hu : Tendsto (Upper C L B) atTop atTop := by
    exact (tendsto_const_mul_atTop_of_pos hL).mpr ((tendsto_rpow_atTop
      (show 0 < B+1 by linarith)).comp (lambda_leads C hG))
  have hw (z : Cover) (_ : z∈X) (i: Axis) := hu.eventually_gt_atTop (2*((z i).natAbs+1):ℝ)
  filter_upwards [inner_bound C hG L B hL,eventually_all_finset X |>.mpr
    (fun z hz => eventually_all.mpr (hw z hz))] with k hi hX
  intro N hN p hp o z hz
  obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hz
  refine Tiling.fits_stencil _ (Stock.centered_margin p hp o) fun j => ?_
  let t := C.S.toDepth hp p
  have h : C.S.a N*(2*((y j).natAbs+1):ℝ)<C.S.a (port C L B hL k) := calc
    _ ≤ C.S.a k*(2*((y j).natAbs+1):ℝ) := mul_le_mul_of_nonneg_right (C.S.strictAnti.antitone hN) (by positivity)
    _ < C.S.a k * Upper C L B k := mul_lt_mul_of_pos_left (hX y hy j) (C.S.a_pos _)
    _ ≤ _ := (mul_comm ..).trans_le (hi.trans (C.S.strictAnti.antitone (Nat.le_succ _)))
  have hh:=h.trans_eq (C.S.embeds_scale t).symm
  have he := lt_of_mul_lt_mul_left hh (C.S.a_pos _).le
  have hn : 2*((y j).natAbs+1)<t.count.val := by exact_mod_cast he
  change (y j).natAbs < t.count.val/2
  omega

end YM.Integration.WilsonMovingReportFootprint
