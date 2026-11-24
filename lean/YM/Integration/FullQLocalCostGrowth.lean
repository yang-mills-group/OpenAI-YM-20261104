import YM.Integration.FullQLocalCostRecipe
import YM.Integration.ActualRunAdmissionClock

/-! A fixed later polynomial coefficient is absorbed by one extra power of
the original admitted cost. The original Run, old schedule and price family
are retained. No coefficient enters the pre-Run recipe selection. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.PreRun.CostProfile
open Filter Lattice RG
open PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep
open scoped Topology

variable {G : Gauge} {V : Type} {C : Family G} {J J' : Request V}

private theorem cover_le_cost (A : NumericSchedule C J) (m : ℕ) :
    (C.path.levels.clock.coverSize m : ℝ) ≤ A.admittedCost m := by
  have h := A.cost_covers_geometry m
  have hp := (C.path.levels.params m).paths_pos
  have hp' := (C.path.levels.params (m + 1)).paths_pos
  have hc := (C.path.levels.params m).columns_ge
  have hc' := (C.path.levels.params (m + 1)).columns_ge
  have hr := (C.path.levels.params m).clip.radius_pos
  have hr' := (C.path.levels.params (m + 1)).clip.radius_pos
  have hm : 0 < C.path.levels.clock.monitor m := Real.exp_pos _
  have hm' : 0 < C.path.levels.clock.monitor (m + 1) := Real.exp_pos _
  have hl := Real.rpow_nonneg hm.le
    (C.path.levels.clock.theta (C.path.levels.clock.J m))
  have hl' := Real.rpow_nonneg hm'.le
    (C.path.levels.clock.theta (C.path.levels.clock.J (m + 1)))
  unfold Calendar.loopCap at h
  linarith [Nat.cast_nonneg (α := ℝ) (C.path.levels.clock.coverSize m),
    Nat.cast_nonneg (α := ℝ) (C.path.levels.clock.coverSize (m + 1))]

/-- Every fixed real coefficient is eventually below the unchanged admitted
cost. The actual log-beta lower bound is already in cost_covers_geometry. -/
theorem eventually_cost_ge (R : Run G) (hG : G.Simple)
    (A : NumericSchedule R.family J) (c : ℝ) :
    ∀ᶠ m : ℕ in atTop, c ≤ A.admittedCost m := by
  have hz := Real.tendsto_log_atTop.comp (WardBin.bell R.family.path.levels hG)
  filter_upwards [hz.eventually_ge_atTop 1, hz.eventually_ge_atTop c] with m h1 hc
  change 1 ≤ Real.log (R.family.path.levels.clock.hatBeta m) at h1
  change c ≤ Real.log (R.family.path.levels.clock.hatBeta m) at hc
  have hsq : c ≤ (Real.log (R.family.path.levels.clock.hatBeta m)) ^ 2 := by
    exact hc.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr h1) (zero_le_one.trans h1)])
  have hceil : (Real.log (R.family.path.levels.clock.hatBeta m)) ^ 2 ≤
      (R.family.path.levels.clock.coverSize m : ℝ) := Nat.le_ceil _
  exact hsq.trans (hceil.trans (cover_le_cost A m))

/-- The next finite recipe pays the full old retuned geometry bill eventually.
The degree is fixed before the Run; the original coefficient is absorbed only
on this later tail, after the same price family is fixed. -/
theorem Recipe.eventually_next_geometry (R : Run G) (hG : G.Simple)
    (e : Recipe) (W : ProfileWidths)
    (A : NumericSchedule R.family J) (hsub : e.Subpower A)
    (hbase : ∀ m, 2 * ActualRunComponentAdmission.cost R.family W m = A.admittedCost m)
    (A' : NumericSchedule R.family J') (K : NumericPrices (e.schedule A hsub))
    (degree order : ℕ) (hdegree : K.polynomialDegree = degree) :
    ∀ᶠ m : ℕ in atTop, (4 : ℝ) ^ order * K.geometry (m + 1) ≤
      (e.next W degree order).cost A' m := by
  filter_upwards [(tendsto_add_atTop_nat 1).eventually
    (eventually_cost_ge R hG (e.schedule A hsub) K.polynomialConstant)] with m hm
  exact e.next_geometry W A hsub hbase A' K degree order m hdegree
    (hm.trans (le_add_of_nonneg_left zero_le_one))

end YM.Integration.FullQLocal.PreRun.CostProfile
end
