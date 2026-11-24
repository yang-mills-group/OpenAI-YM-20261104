import YM.Integration.ActualRunRequestedWidth
import YM.Extra.WILSON_STARTUP.Clock
import YM.Next.WARD_BIN.Hats
import YM.Progress.DIRECTED_RECIPE.Batch

/-! The original startup gas has a full invoice at every fixed requested
order, power and positive support exponent. The calendar and every payload
row are unchanged. Native Timing.loan pays the complete fixed-drawer merger. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualStartupRequestedBudget

open Filter Lattice RG Wilson WilsonStartup
open RG.Shoot PhysicalNext.Repeat.Legato
open Progress.DirectedRecipe ActualRunAdmissionScales
open scoped Topology

variable {G : Gauge}

/-- The original calendar pays the complete startup ingredients at a fixed
requested norm on one tail before all periods and all couplings in its band. -/
theorem eventually_ingredients (R : Run G) (hG : G.Simple)
    (ord pow : ℕ) (supp : ℝ)
    (hord : 6 ≤ ord) (hpow : 2 ≤ pow) (hsupp : 0 < supp) :
    ∀ᶠ N : ℕ in atTop, ∀ (period : ℕ) (beta : ℝ),
      beta ∈ band R.family.path.levels N →
      let q := requestedBudget R.family.path.levels N ord pow supp hord hpow hsupp
      Ingredients (Start.dictionary G (R.family.side N period))
        (Start.payload (R.family.path.levels.params N).clip q G
          (R.family.side N period) beta) q
        (R.family.path.levels.clock.allowance N)
        (R.family.path.levels.clock.forcedAllowance N) := by
  let A := R.family.path.levels
  let S : Stage := { A.params 0 with
    order := ord
    power := pow
    supportExponent := supp
    order_ge := hord
    power_ge := hpow
    price_pos := hsupp }
  have hlog : Tendsto (fun N : ℕ => Real.log (A.clock.hatBeta N)) atTop atTop :=
    Real.tendsto_log_atTop.comp (WardBin.bell A hG)
  have hsmall : ∀ᶠ s : ℝ in atTop,
      Timing.temp s ≤ Start.threshold G ord pow :=
    Timing.shrinking.eventually (ge_mem_nhds (Start.constants G ord pow).2.1)
  filter_upwards [hlog.eventually hsmall, hlog.eventually (Timing.afford G S),
    hlog.eventually (Timing.loan supp)] with N hsmall hafford hloan
  intro period beta hbeta
  let q := requestedBudget A N ord pow supp hord hpow hsupp
  have hx : 0 < A.clock.hatBeta N := zero_lt_one.trans (A.fits.delayed N)
  have hb : q.B = Timing.balls (Real.log (A.clock.hatBeta N)) := rfl
  have hp : (Real.sqrt (A.clock.hatBeta N))⁻¹ =
      Real.exp (-(Real.log (A.clock.hatBeta N) / 2)) := by
    rw [Real.exp_neg, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    congr 2
    ring
  have ht : q.threshold = Timing.temp (Real.log (A.clock.hatBeta N)) := by
    change (Real.sqrt (A.clock.hatBeta N))⁻¹ * Real.exp _ = _
    unfold Timing.temp
    rw [hp, Real.exp_add]
  have he : A.clock.allowance N = Timing.normE (Real.log (A.clock.hatBeta N)) := by
    unfold Calendar.allowance Calendar.hatCoupling Timing.normE
    rw [hp, ← Real.exp_mul]
    congr 1
    ring
  have hw : A.clock.forcedAllowance N = Timing.normK (Real.log (A.clock.hatBeta N)) := by
    unfold Calendar.forcedAllowance Calendar.monitor Timing.normK
    rw [← Real.exp_mul]
    congr 3
    ring
  have hd0 := (ActualRunRequestedWidth.native_geometry R N).1
  have hd : Decent (A.params N).clip q := ⟨hd0.direct, hd0.radius, hd0.cut⟩
  have hr : q.threshold ≤ Start.threshold G q.order q.power := by
    change q.threshold ≤ Start.threshold G ord pow
    rw [ht]
    exact hsmall
  obtain ⟨hLoan, hQuote⟩ := hloan q ht hb rfl
  rw [Real.exp_log hx] at hLoan
  have hbook : Start.book G q (2 * A.clock.hatBeta N) ≤ A.clock.allowance N := by
    calc
      _ = Start.book G q (2 * Real.exp (Real.log (A.clock.hatBeta N))) := by
        rw [Real.exp_log hx]
      _ ≤ Timing.normE (Real.log (A.clock.hatBeta N)) := hafford q rfl rfl rfl ht
      _ = A.clock.allowance N := he.symm
  have hn : ‖beta‖ ≤ 2 * A.clock.hatBeta N := by
    rw [Real.norm_of_nonneg (hLoan.slope.trans hbeta.1)]
    exact hbeta.2
  have hm : Start.book G q ‖beta‖ ≤ Start.book G q (2 * A.clock.hatBeta N) := by
    unfold Start.book Start.overhead
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hn (Start.item_pos G q).le)
        (Real.exp_pos _).le)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  refine ⟨?_⟩
  exact ⟨Timing.M (Real.log (A.clock.hatBeta N)),
    Real.exp (Timing.quota (Real.log (A.clock.hatBeta N))) - 1,
    Real.exp (Timing.quota (Real.log (A.clock.hatBeta N))) - 1,
    Start.digests hd hr hLoan hbeta.1 (hm.trans hbook),
    hLoan.buys hd hbeta.1, hQuote.trans_eq hw.symm⟩

/-- The same complete startup payload is valid after the actual fixed-drawer
merger. The path and scalar are arbitrary because neither changes its rows. -/
theorem eventually_valid (R : Run G) (hG : G.Simple)
    (ord pow : ℕ) (supp : ℝ)
    (hord : 6 ≤ ord) (hpow : 2 ≤ pow) (hsupp : 0 < supp) :
    ∀ᶠ N : ℕ in atTop, ∀ (period : ℕ) (beta : ℝ),
      beta ∈ band R.family.path.levels N →
      ∀ (W : PathData G) (v : ℝ),
      let q := requestedBudget R.family.path.levels N ord pow supp hord hpow hsupp
      (finish W (R.family.path.levels.params N).clip q
        (Start.dictionary G (R.family.side N period))
        (Start.payload (R.family.path.levels.params N).clip q G
          (R.family.side N period) beta) beta v).activities.Valid q
        (R.family.path.levels.clock.allowance N)
        (R.family.path.levels.clock.forcedAllowance N) := by
  filter_upwards [eventually_ingredients R hG ord pow supp hord hpow hsupp] with N hN
  intro period beta hbeta W v
  exact (hN period beta hbeta).gates W _ beta v

end YM.Integration.ActualStartupRequestedBudget
end
