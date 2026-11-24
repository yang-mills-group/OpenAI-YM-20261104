import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Spend the physical holomorphic tube in a genuine real test direction
before multiplying by the spatial cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalDiscJets
open Set Filter Metric Complex
open scoped Topology ContDiff

private theorem analytic (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f U) (n : ℕ) : DifferentiableOn ℂ (iteratedDeriv n f) U := by
  induction n with
  | zero => simpa
  | succ n ih => rw [iteratedDeriv_succ];exact ih.deriv hU

theorem restriction (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f U) (n : ℕ) (x : ℝ) (hx : (x:ℂ) ∈ U) :
    iteratedDeriv n (fun y : ℝ => f y) x = iteratedDeriv n f (x:ℂ) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have same : iteratedDeriv n (fun y : ℝ => f y) =ᶠ[𝓝 x]
        fun y : ℝ => iteratedDeriv n f (y:ℂ) := by
      filter_upwards [(hU.preimage Complex.continuous_ofReal).mem_nhds hx] with y hy
      exact ih y hy
    have diff := (analytic U hU f hf n).differentiableAt (hU.mem_nhds hx)
    simp only [iteratedDeriv_succ]
    exact same.deriv_eq.trans diff.hasDerivAt.comp_ofReal.deriv

/-- At a fixed radius the complex continuation can be local to the submitted
point and coordinate. Only its germ enters the measured real derivative. -/
theorem original (F : ℂ → ℂ) (f : ℝ → ℂ) (x w M : ℝ) (hw : 0 < w)
    (continues : f =ᶠ[𝓝 x] fun t : ℝ => F t)
    (holomorphic : DiffContOnCl ℂ F (ball (x:ℂ) w))
    (size : ∀ z ∈ sphere (x:ℂ) w, ‖F z‖ ≤ M) (n : ℕ) :
    ‖iteratedDeriv n f x‖ ≤ n.factorial * M / w^n := by
  rw [Filter.EventuallyEq.iteratedDeriv_eq n continues,
    restriction _ isOpen_ball F holomorphic.differentiableOn n x (mem_ball_self hw)]
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hw holomorphic size

end YM.Integration.WilsonOriginalPhysicalDiscJets

