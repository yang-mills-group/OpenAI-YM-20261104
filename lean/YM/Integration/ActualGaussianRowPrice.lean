import YM.Integration.NativePaidCovarianceRows
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Issue.Glyph
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Actual free-coordinate Gaussian row payment

Restrict the original native covariance row along its injective free-coordinate
plant. The selected kernel is the same step of the supplied Chain on the
original Run. The complex Gaussian covariance is the literal realRank cast.

No horizon equality or new covariance estimate is assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualGaussianRowPrice
open Function Lattice RG Precision Tree
open RG08.Line Comparison.RG02 PhysicalNext.Repeat.Legato
open PhysicalNext.WeightedGaussianMarginal45C
open scoped BigOperators Classical

private theorem sum_injection {I J : Type*} [Fintype I] [Fintype J]
    (e : I → J) (he : Injective e) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) :
    (∑ i, f (e i)) ≤ ∑ j, f j := by
  rw [← Finset.sum_image (f := f) (g := e) (s := Finset.univ) he.injOn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun j _ _ => hf j)

variable {G : Gauge} (R : Run G) (Y : Bulk.Chain R.family.path)
    (hAttached : ActualRunNativeComponentRecipe.Attached R)
    (N period m : ℕ) (hm : m < N)

local notation "a₀" => R.family.path.levels
local notation "S₀" => R.family.path.levels.clock.op m period
local notation "F₀" => green (R.family.path.levels.clock.op m period)
local notation "K₀" => Y.step N m period hm

include hAttached in
/-- The complete Gaussian row in the original free-coordinate basis.
The full native spatial/color factor and its logarithmic power are retained. -/
theorem row_bound (t : (S₀).Choices) (i : Precision.Key F₀ G) :
    (∑ j : Precision.Key F₀ G,
      ‖(Issue.realRank ((K₀).covariance F₀ t) ((K₀).symm F₀ t)).cov i j‖) ≤
      (Fintype.card (Stationary.Loc G 1) : ℝ) * Real.exp 8 *
        (Real.log ((a₀).clock.hatBeta m)) ^ 5 := by
  simp only [Issue.realRank, Complex.norm_real, Real.norm_eq_abs]
  rw [ActualNativeKernelDictionary.actual_covariance R Y N period m hm t]
  change
    (∑ j : Precision.Key F₀ G,
      |NativeLine S₀ G (R.alloy.B.M.H N (m + 1))
        (FreeResolvent.plant F₀ i) (FreeResolvent.plant F₀ j)|) ≤ _
  have hrestrict := sum_injection
    (FreeResolvent.plant (G := G) F₀) (FreeResolvent.plant_inj F₀)
    (fun j => |NativeLine S₀ G (R.alloy.B.M.H N (m + 1))
      (FreeResolvent.plant F₀ i) j|) (fun _ => abs_nonneg _)
  have hpaid := NativePaidCovarianceRows.covariance_row R hAttached
    N period m hm (FreeResolvent.plant F₀ i)
  simpa only [mul_assoc] using hrestrict.trans hpaid

end YM.Integration.ActualGaussianRowPrice
end
