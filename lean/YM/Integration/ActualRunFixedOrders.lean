import YM.FullVolume.Cross

/-!
Numerical derivative-order admission on the original Run.

The original constructor already chooses a profile with jets = 6+j and
position = 2+j. Its separately forwarded profile receipt is used literally
here. Generic Fits.deepOrder/deepPower are only monotonicity and are not
treated as divergence. No new schedule, Run or analytic estimate is chosen.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunFixedOrders

open Filter RG PhysicalNext.Repeat.Legato
open scoped Topology

variable {G : Gauge}

/-- The constructor's original profile receipt gives both actual budget
orders at every stage, before any cutoff or period is chosen. -/
theorem budget_orders (R : Run G)
    (hprofile : ∀ j, j ≤ (R.metals.p.profile j).order ∧
      j ≤ (R.metals.p.profile j).power) (m : ℕ) :
    R.family.path.levels.clock.J m ≤
        (R.family.path.levels.budget m).order ∧
      R.family.path.levels.clock.J m ≤
        (R.family.path.levels.budget m).power := by
  change R.alloy.B.a.clock.J m ≤
      (R.alloy.B.a.clock.stage (R.alloy.B.a.clock.J m)).order ∧
    R.alloy.B.a.clock.J m ≤
      (R.alloy.B.a.clock.stage (R.alloy.B.a.clock.J m)).power
  rw [R.alloy.B.valid.stage]
  exact hprofile (R.alloy.B.a.clock.J m)

/-- Every fixed field/distance request is admitted at the original fine
stage after one event independent of cutoff and period. The profile premise
is the literal finite-order receipt retained by the original constructor. -/
theorem eventually_orders (R : Run G)
    (hprofile : ∀ j, j ≤ (R.metals.p.profile j).order ∧
      j ≤ (R.metals.p.profile j).power)
    (fieldOrder distanceOrder : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      fieldOrder ≤ (R.family.path.levels.budget (m + 1)).order ∧
      distanceOrder ≤ (R.family.path.levels.budget (m + 1)).power := by
  have hdeep := R.family.path.levels.fits.deep.eventually_ge_atTop
    (max fieldOrder distanceOrder)
  filter_upwards [hdeep] with m hm
  have hnext : max fieldOrder distanceOrder ≤
      R.family.path.levels.clock.J (m + 1) :=
    hm.trans (R.family.path.levels.fits.mono (Nat.le_succ m))
  obtain ⟨horder, hpower⟩ := budget_orders R hprofile (m + 1)
  exact ⟨((le_max_left _ _).trans hnext).trans horder,
    ((le_max_right _ _).trans hnext).trans hpower⟩

end YM.Integration.ActualRunFixedOrders
end
