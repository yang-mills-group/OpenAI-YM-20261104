import YM.Integration.FullQLocalCostProfileNumerics

/-! Literal finite recipes for the next admitted cost. The extra power absorbs
a later fixed polynomial coefficient; no coefficient is used to select a recipe.
This file proves the pointwise algebra only. Actual subpower and eventual
coefficient domination remain separate numerical obligations. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.PreRun.CostProfile
open Lattice RG
open FullQLocal.RenderedStep

/-- The complete old admitted cost as one finite expression. -/
def Recipe.total (e : Recipe) (W : ProfileWidths) : Polynomial :=
  match e with
  | .keep => .profile W
  | .enlarge extra => .add (.profile W) extra

variable {G : Gauge} {V : Type} {C : Family G} {J J' : Request V}

theorem Recipe.total_eval (e : Recipe) (W : ProfileWidths)
    (A : NumericSchedule C J)
    (hbase : ∀ m, 2 * ActualRunComponentAdmission.cost C W m = A.admittedCost m)
    (m : ℕ) :
    (e.total W).eval C m = e.cost A m := by
  cases e <;> simp only [Recipe.total, Polynomial.eval, Recipe.cost, hbase]

/-- One extra power of the previous shifted cost is reserved before the Run.
The old fixed degree and requested retuning order are the only parameters. -/
def Recipe.next (e : Recipe) (W : ProfileWidths) (degree order : ℕ) : Recipe :=
  .enlarge (.mul (.constant (4 ^ order))
    (.pow (.add (.constant 1) (.shift (e.total W) 1)) (degree + 1)))

theorem Recipe.next_cost (e : Recipe) (W : ProfileWidths)
    (degree order : ℕ) (A : NumericSchedule C J') (m : ℕ) :
    (e.next W degree order).cost A m =
      A.admittedCost m + (4 : ℝ) ^ order *
        (1 + (e.total W).eval C (m + 1)) ^ (degree + 1) := by
  simp only [Recipe.next, Recipe.cost, Polynomial.eval, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_one]

/-- The original geometry bill is paid on the same old price family.
The coefficient bound is an explicit pointwise premise here, to be discharged
eventually after that family is fixed. -/
theorem Recipe.next_geometry (e : Recipe) (W : ProfileWidths)
    (A : NumericSchedule C J) (hsub : e.Subpower A)
    (hbase : ∀ m, 2 * ActualRunComponentAdmission.cost C W m = A.admittedCost m)
    (A' : NumericSchedule C J') (K : NumericPrices (e.schedule A hsub))
    (degree order m : ℕ) (hdegree : K.polynomialDegree = degree)
    (hconstant : K.polynomialConstant ≤
      1 + (e.schedule A hsub).admittedCost (m + 1)) :
    (4 : ℝ) ^ order * K.geometry (m + 1) ≤
      (e.next W degree order).cost A' m := by
  have hcost := congrFun (e.schedule_data A hsub).2.2.2.2.2.2.2 (m + 1)
  rw [e.next_cost, e.total_eval W A hbase, ← hcost]
  let x : ℝ := 1 + (e.schedule A hsub).admittedCost (m + 1)
  have hx : 0 ≤ x :=
    add_nonneg zero_le_one ((e.schedule A hsub).admitted_cost_nonnegative (m + 1))
  have hb : K.geometry (m + 1) ≤ K.polynomialConstant * x ^ degree := by
    simpa only [hdegree] using K.polynomial_bound (m + 1)
  have hp : K.polynomialConstant * x ^ degree ≤ x ^ (degree + 1) := by
    calc
      _ ≤ x * x ^ degree :=
        mul_le_mul_of_nonneg_right hconstant (pow_nonneg hx degree)
      _ = x ^ (degree + 1) := (pow_succ' x degree).symm
  exact (mul_le_mul_of_nonneg_left (hb.trans hp) (by positivity)).trans
    (le_add_of_nonneg_left (A'.admitted_cost_nonnegative m))

end YM.Integration.FullQLocal.PreRun.CostProfile
end
