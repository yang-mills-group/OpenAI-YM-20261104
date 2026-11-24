import YM.Pert.Fourier.Modes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Geometry
/-! Slow-wave probes at wavelength equal to the actual physical period in lattice units.
Two real components allow a uniform pointwise non-degenerate curvature energy. -/
noncomputable section
set_option autoImplicit false
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson RG
open scoped Topology BigOperators Classical ContDiff
variable {n : Side}

lemma sep_self (a : Site n) : separation a a = 0 := by simp [separation,pdist,lift]
lemma lift_step_large (hn : 4 ≤ n.val) (d : Axis) : lift (step d : Site n) = step d := by
   have hx : 10 * separation (0:Site n) (0:Site n) < n.val := by rw [sep_self]; omega
   simpa [Step.vec_pos,lift] using (AnalyticBridge.VerifiedReset.lift_step (o:=0) (x:=0) hx hn (posDir d))

private lemma phase_unit (hn : 4 ≤ n.val) (d : Axis) (u : Cover) : Full.char (step d : Site n) (wrap n u) =
    Complex.exp (((↑(Full.mesh n * (u d : ℝ))):ℂ) * Complex.I) := by
   rw [Full.char_wrapped]
   have e : Full.corner u (Full.moment (n:=n) (step d)) = Full.mesh n * (u d:ℝ) := by
      simp_rw [Full.corner,Full.moment_apply,lift_step_large hn,step_apply]
      rw [Finset.sum_eq_single d] <;> simp_all <;> ring_nf
   simp [e]
/-- Real rather than complex for use as actual potential-field directions. Signed versions
 can have either transverse sign. -/
def mode (d : Axis) (b : Bool) (x : Site n) : ℝ := if b then (Full.char (step d) x).im else (Full.char (step d) x).re

def trig (b : Bool) : ℝ → ℝ := if b then Real.sin else Real.cos
lemma mode_wrap (hn : 4 ≤ n.val) (d : Axis) (u : Cover) (b : Bool) : mode d b (wrap n u) = trig b (Full.mesh n * (u d:ℝ)) := by
   unfold mode trig
   simp only [phase_unit hn,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin, Complex.add_im, Complex.add_re,Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im, Complex.mul_re]
   cases b <;> simp
lemma trig_lip (b : Bool) (x y : ℝ) : |trig b x-trig b y| ≤ |x-y| := by
   cases b; exact Real.abs_cos_sub_cos_le ..; exact Real.abs_sin_sub_sin_le ..
lemma deriv_trig_lip (b : Bool) (x y : ℝ) : |deriv (trig b) x - deriv (trig b) y| ≤ |x-y| := by
   cases b
   · change |deriv Real.cos x - deriv Real.cos y| ≤ _
     convert trig_lip true x y using 1; simp only [Real.deriv_cos]; rw [neg_sub_neg,abs_sub_comm];rfl
   change |deriv Real.sin x - deriv Real.sin y| ≤ _; simp [Real.deriv_sin,Real.abs_cos_sub_cos_le]
lemma deriv_trig_diff (b : Bool) : Differentiable ℝ (trig b) := by cases b; exact Real.differentiable_cos; exact Real.differentiable_sin

end YM.Pert.Kinetic
