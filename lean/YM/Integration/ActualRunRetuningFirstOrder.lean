import YM.Integration.ActualRunBetaResetDomain
import YM.Integration.ActualBetaAllOrderCost

/-!
The complete finite-copy bill on the original Run differs from one by at
most a cap-only constant times its actual relative beta increment. The
bound includes zero truncation order. The Run supplies the half-radius
domain and positivity before the cutoff, period, exponent and copy order.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunRetuningFirstOrder

open Filter RG PhysicalNext.Repeat.Legato Pert.Asymptotics
open MatchingLedger.Compass.Income ActualBetaRemainder
open scoped Topology

theorem uniform_cost (cap : ℕ) :
    ∃ D > 0, ∀ {G : Gauge} (R : Run G), G.Simple →
      ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N →
        ∀ e : ℤ, |e| ≤ (cap : ℤ) → ∀ n : ℕ,
          coefficientBill e
              (R.family.path.β N p m - R.family.path.β N p (m + 1))
              (regulatorRun R.family N p m) n +
            |correctionCoefficient e
              (R.family.path.β N p m - R.family.path.β N p (m + 1))
              (regulatorRun R.family N p m) n| *
              |regulatorRun R.family N p m| ^ (2 * n) ≤
            1 + D * |(R.family.path.β N p m - R.family.path.β N p (m + 1)) *
              regulatorRun R.family N p m ^ 2| := by
  obtain ⟨D, hD, hbound⟩ := full_retuning_all_orders cap
  refine ⟨D, hD, ?_⟩
  intro G R hG
  filter_upwards [ActualRunBetaResetDomain.half_radius R hG] with m hm
  intro N p hN e he n
  exact hbound e he _ _ (Weather.runs_pos R.family R.makes hN.le p).ne'
    (hm N p hN) n

/-- The same constant works simultaneously at every level above the
original diverging lower endpoint, before all periods and copy orders. -/
theorem window_uniform_cost (cap : ℕ) :
    ∃ D > 0, ∀ {G : Gauge} (R : Run G), G.Simple →
      ∀ {ι : Type*} {l : Filter ι} (lower : ι → ℕ), Tendsto lower l atTop →
        ∀ᶠ a in l, ∀ m : ℕ, lower a ≤ m → ∀ N p : ℕ, m < N →
          ∀ e : ℤ, |e| ≤ (cap : ℤ) → ∀ n : ℕ,
            coefficientBill e
                (R.family.path.β N p m - R.family.path.β N p (m + 1))
                (regulatorRun R.family N p m) n +
              |correctionCoefficient e
                (R.family.path.β N p m - R.family.path.β N p (m + 1))
                (regulatorRun R.family N p m) n| *
                |regulatorRun R.family N p m| ^ (2 * n) ≤
              1 + D * |(R.family.path.β N p m - R.family.path.β N p (m + 1)) *
                regulatorRun R.family N p m ^ 2| := by
  obtain ⟨D, hD, hbound⟩ := uniform_cost cap
  refine ⟨D, hD, ?_⟩
  intro G R hG ι l lower hlower
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hbound R hG)
  filter_upwards [hlower.eventually (eventually_ge_atTop M)] with a ha
  intro m hm N p hN e he n
  exact hM m (ha.trans hm) N p hN e he n

end YM.Integration.ActualRunRetuningFirstOrder
end
