import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue

/-! Finite translations of a smooth spatial test cost exactly their own derivative order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabDifferences
open Function Set
open scoped Topology ContDiff
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]

def move (h:E)(f:E→F)(x:E):F:=f (x+h)-f x

def steps (h:E):ℕ→(E→F)→(E→F)
  | 0,f=>f
  | n+1,f=>steps h n (move h f)

private theorem smooth (h:E){f:E→F}(good:ContDiff ℝ ∞ f):ContDiff ℝ ∞ (move h f):=
  (good.comp (contDiff_id.add contDiff_const)).sub good

theorem paid (n:ℕ)(h:E)(f:E→F)(good:ContDiff ℝ ∞ f)(B:ℝ)
    (bound:∀x,‖iteratedFDeriv ℝ n f x‖≤B)(x:E): ‖steps h n f x‖≤B*‖h‖^n:=by
  induction n generalizing f B x with
  | zero=>simpa [steps,norm_iteratedFDeriv_zero] using bound x
  | succ n ih=>
    have next (z:E):‖iteratedFDeriv ℝ n (move h f) z‖≤B*‖h‖:=by
      change ‖iteratedFDeriv ℝ n ((fun w:E=>f (w+h))-f) z‖≤_
      have moved:ContDiff ℝ n (fun w:E=>f (w+h)):=contDiff_infty.mp (good.comp (contDiff_id.add contDiff_const)) n
      rw [iteratedFDeriv_sub moved (contDiff_infty.mp good n),Pi.sub_apply,iteratedFDeriv_comp_add_right]
      have priced:= (convex_univ (𝕜:=ℝ) (E:=E)).norm_image_sub_le_of_norm_fderiv_le
        (f:=iteratedFDeriv ℝ n f) (fun y _=>((contDiff_infty.mp good (n+1)).contDiffAt.differentiableAt_iteratedFDeriv (m:=n) (Nat.cast_lt.mpr n.lt_succ_self)))
        (fun y _=>by rw [norm_fderiv_iteratedFDeriv]; exact bound y) (mem_univ z) (mem_univ (z+h))
      simpa only [add_sub_cancel_left] using priced
    calc
      ‖steps h (n+1) f x‖ ≤ (B*‖h‖)*‖h‖^n:=ih (move h f) (smooth h good) (B*‖h‖) next x
      _ = B*‖h‖^(n+1):=by ring

end YM.Integration.WilsonSeparatedOriginalSlabDifferences
