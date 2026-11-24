import YM.Integration.WilsonConditionalTaylorSceneCalibration
import YM.Integration.WilsonConditionalTaylorKineticRebooking

/-! Identify the genuine physically issued coupling reset with the
independent scalar functional evaluated at its measured finite-torus
two-leg primitive. This preserves the direction of the physical tilt. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorSceneReset

open PowerSeries Lattice RG Wilson Precision Exterior Push.Uniform MSbar MSbar.Cacao MSbar.Rolling
open MSbar.Midpoint MSbar.Wave FormalBulk08 FormalBulk08.Series PhysicalNext.Repeat.Legato
open WilsonConditionalTaylorSceneCalibration WilsonConditionalTaylorKineticRebooking
open scoped Classical

variable {G : Gauge} (R : Run G) {N n k r : ℕ} {S : Scene R.family.path.levels n r} {u : G.ColorIndex}
  (scene : Realized R.alloy.B.kin N n k r (Lis.sun G u) S)

def measured (j : ℕ) (lo : k ≤ j) (hi : j < N) : PowerSeries ℝ :=
  primitive (Lis.sun G u) (untuned R scene j lo hi) (inkAt R N n j)

theorem original (j : ℕ) (lo : k ≤ j) (hi : j < N)
    (finance : Alto.Sampled (R.family.side j n) (R.family.path.levels.params j)) :
    Through r (S.action j) (Wine.bookU (measured R scene j lo hi)) ∧
      Through r (S.action j)⁻¹ (Wine.bookH (measured R scene j lo hi)) := by
  let T:=untuned R scene j lo hi
  let K:=inkAt R N n j
  let z:=caliper (R.family.side j n) (Lis.sun G u)
  let H:=measured R scene j lo hi
  have level : |z K+2|≤1:=charged R scene j lo hi.le finance
  have den : z K≠0 := by intro h; rw [h,zero_add,abs_of_nonneg (by norm_num)] at level; norm_num at level
  obtain ⟨head,kind,_,_⟩:=received R scene j lo hi
  have clear (i : ℕ) : z (coeff i (bley (Wine.bookU H) T K))=0 := by
    have h:=congrArg (coeff i) (clears (Lis.sun G u) T K kind den)
    change caliper (R.family.side j n) (Lis.sun G u) (coeff i (bley (Wine.bookU (primitive (Lis.sun G u) T K)) T K))=0
    simpa only [projection,coeff_mk,map_zero] using h
  have fixed : Through r (S.action j) (Wine.bookU H) := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i previous =>
      intro due
      by_cases unpaid : i=0
      · subst i; exact head.trans (Wine.book_guard H).symm
      have earlier : Hush (S.action j) (Wine.bookU H) i := fun l hl=>previous l hl (by omega)
      have h:=unsettled R scene j lo hi (Wine.bookU H) (Nat.pos_of_ne_zero unpaid) due earlier
      change z (coeff i (bley (Wine.bookU H) T K))= -(2*(coeff i (Wine.bookU H)-coeff i (S.action j))*z K) at h
      rw [clear] at h
      have product : 2*(coeff i (Wine.bookU H)-coeff i (S.action j))*z K=0 := by linarith only [h]
      exact (sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp product).resolve_right den)).resolve_left (by norm_num))).symm
  refine ⟨fixed,?_⟩
  have earlier : Hush (S.action j) (Wine.bookU H) (r+1) := fun i hi=>fixed i (by omega)
  intro i link
  simpa only [WilsonConditionalTaylorKineticRebooking.inverse] using earlier.invH i (by omega)

end YM.Integration.WilsonConditionalTaylorSceneReset
end

