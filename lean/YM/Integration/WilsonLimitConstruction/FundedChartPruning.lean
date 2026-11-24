import YM.Integration.WilsonLimitConstruction.FundedChartDemand
import YM.Integration.WilsonLimitConstruction.FundedPruningRate
import YM.RG01Estimate.Posting

/-! The actual inherited coupon and the wage of the original selected chart
issue have a joint raw-monitor estimate on the physical calendar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedChartPruning

open Filter Lattice RG FullQLocal.RawInherited PhysicalNext.Repeat.Legato RG01Estimate
open RG01Estimate.Chart
open scoped Topology

variable {G : Gauge}

theorem debit_nonneg {n : Side} {V : Rep G n} {E : Set ℕ} {τ : ℝ}
    (h : Inherit.Debits V E τ) : 0 ≤ τ := by
  obtain ⟨_, _, hSites⟩ := h
  exact Push.AbsoluteSums.budget_nonneg (hSites 0)

theorem retention (R : Run G) (φ W n : ℕ → ℕ → ℕ)
    (H : Stamped (policy G φ W n) R.kit) (m : ℕ) :
    Routed.retention R.kit m ≤ 1 := by
  refine (H.earned m).trans ?_
  exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left
    (Nat.cast_nonneg (α:=ℝ) (R.alloy.B.a.clock.J (m+1))))

/-- The chart supplies at least one real issue at every sufficiently late
level. Every issue there pays the exact two terms entering the delivered
activity norm, for every supported input debit and every cutoff and period. -/
theorem delivery (R : Run G) (hG : G.Simple) (φ W n : ℕ → ℕ → ℕ)
    (H : Stamped (policy G φ W n) R.kit) (r : ℕ) (hr : 2 ≤ r)
    (η : ℝ) (hη : η < 1/2) :
    ∀ᶠ m : ℕ in atTop,
      Nonempty (Issue R.kit (policy G φ W n) m r) ∧
      ∀ I : Issue R.kit (policy G φ W n) m r, ∀ N p : ℕ, m < N →
      ∀ (V : Rep G (R.family.side (m+1) p)) (E : Set ℕ) (τ B : ℝ),
      Inherit.Debits V E τ → 0 ≤ B →
      τ ≤ B * Pert.Asymptotics.regulatorRun R.family N p (m+1) ^ ((r : ℝ)+1-η) →
      let g := Pert.Asymptotics.regulatorRun R.family N p (m+1)
      let w := Precise.wage R.rolls (R.alloy.B.a.clock.adm (m+1))
        I.horizon I.folio (R.alloy.B.a.clock.hatBeta m)
      Routed.retention R.kit m * τ + g^(r+1)*w ≤
        2*(B+1) * shape R.family.path.levels.clock 0 (m+1) := by
  have shifted := tendsto_add_atTop_nat 1
  filter_upwards [shifted.eventually (FundedPruningRate.regulator_power R hG),
      (R.alloy.B.a.fits.deep.comp shifted).eventually_ge_atTop r] with m hPower hPosted
  refine ⟨posts _ R.kit H m r hPosted, ?_⟩
  intro I N p hm V E τ B hDebit hB hτ
  let j := R.alloy.B.a.clock.J (m+1)
  let i := R.alloy.B.a.clock.J m
  let loss := ((policy G φ W n).wish R.rolls j i r).loss
  let g := Pert.Asymptotics.regulatorRun R.family N p (m+1)
  let rate := shape R.family.path.levels.clock 0 (m+1)
  let w := Precise.wage R.rolls (R.alloy.B.a.clock.adm (m+1))
    I.horizon I.folio (R.alloy.B.a.clock.hatBeta m)
  have hl : loss ≤ 1 := inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg j))
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hBand : R.family.path.β N p (m+1) ∈ Shoot.band R.alloy.B.a (m+1) :=
    (R.makes.wilson.represents N p (m+1) hm).band
  have hw : g^(r+1)*w ≤ g^((r : ℝ)+1-loss) := I.scaled _ hBand
  have hFee : g^(r+1)*w ≤ 2*rate :=
    hw.trans (hPower N p hm _ (by linarith only [hr', hl]))
  have hCoupon : τ ≤ B*(2*rate) :=
    hτ.trans (mul_le_mul_of_nonneg_left
      (hPower N p hm _ (by linarith only [hr', hη])) hB)
  calc
    _ ≤ 1*τ + 2*rate := add_le_add
      (mul_le_mul_of_nonneg_right (retention R φ W n H m) (debit_nonneg hDebit)) hFee
    _ ≤ 1*(B*(2*rate)) + 2*rate :=
      add_le_add (mul_le_mul_of_nonneg_left hCoupon zero_le_one) le_rfl
    _ = 2*(B+1)*rate := by ring

end YM.Integration.WilsonLimitConstruction.FundedChartPruning
end
