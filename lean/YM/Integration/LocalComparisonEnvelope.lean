import YM.Integration.LocalComparisonInterface

/-! Relative kernel prices for the local-comparison vocabulary.

The physical polynomial is not rescaled. Only the coefficient functions
whose common majorants define its relative norm are divided by the announced
input kernel envelopes. In an application these envelopes are the products
for the specified disjoint analytic inputs; they are fixed before the tests,
conditioning fields and output representation are chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker RG3.Script.Picnic
open scoped BigOperators

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V]
    {R : Census V} {X : Type*} {P : Rep G n} {o : V → Site n}

/-- The product convention when an input envelope is attached to each
independent slot. More general disjoint input blocks can provide their
already computed mode envelope directly to `relativeBudget`. -/
def envelopeProduct (cost : V → ℝ) (mode : R.Mode) : ℝ :=
  ∏ v ∈ mode.val, cost v

/-- Coefficient rescaling for a relative norm, with all origins, supports
and marker modes retained literally. This is not asserted to be the
physical output or a new vacuum construction. -/
def priceNormalized (cost : R.Mode → ℝ) (T : Taste X o P R) : Taste X o P R where
  menu :=
    { origins := T.menu.origins
      rays := T.menu.rays
      branch := T.menu.branch
      marks := T.menu.marks
      global := fun x v => (cost (R.fire v))⁻¹ • T.menu.global x v
      regular := fun x i U => (cost (T.menu.rays i))⁻¹ • T.menu.regular x i U
      force := fun x i j U => (cost (T.menu.marks i j))⁻¹ • T.menu.force x i j U }
  root := T.root
  tag := T.tag
  site := T.site
  score := fun x i => (cost (T.tag i))⁻¹ • T.score x i

/-- Exact native full norm after division by the declared products of
analytic input envelopes. No positivity or size of these envelopes is
inferred; a supplier must retain their original prices. -/
structure RelativeBudget (p : BudgetPoint) (T : Taste X o P R)
    (w : V → ℝ) (κ : ℝ) (cost : R.Mode → ℝ)
    (regularPrice forcedPrice : ℝ) where
  positive mode : 0 < cost mode
  quiet : cost R.quiet = 1
  budget : FullBudget p (priceNormalized cost T) w κ regularPrice forcedPrice

end YM.Integration.LocalComparison
