import YM.Integration.WilsonLimitConstruction.FundedSurplusPrice
import YM.Integration.FullQLocalNumericMarkedRateBound

/-! The finite ordinary bill includes the true geometry times the old regular
price. A strictly positive finite-depth margin pays this multiplier uniformly
before every cutoff, period, analytic input and preparation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedOrdinaryReentry
open Filter Lattice Wilson RG Marker PhysicalNext.Repeat.Legato IterationFour
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Pert.Asymptotics
open scoped Topology

private theorem transfer {u T gf gc s a c : ℝ} (hf : 0 < gf) (hc : 0 ≤ gc)
    (hu : 0 ≤ u) (hcomp : gf^s ≤ T*gc^s) (hsmall : u*T*gf^a ≤ c) :
    u*gf^(s+a) ≤ c*gc^s := by
  calc
    u*gf^(s+a) = (u*gf^a)*gf^s := by rw [Real.rpow_add hf]; ring
    _ ≤ (u*gf^a)*(T*gc^s) :=
      mul_le_mul_of_nonneg_left hcomp (mul_nonneg hu (Real.rpow_nonneg hf.le _))
    _ = (u*T*gf^a)*gc^s := by ring
    _ ≤ c*gc^s := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hc _)

variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {Γ : Census V}

/-- Every ordinary exponent below two is available with freely prescribed
positive output coefficient when the previous regular bill carries a surplus. -/
theorem price (R : Run G) (hG : G.Simple) (J : Request V)
    (A : NumericSchedule R.family J) (K : NumericPrices A)
    (eta : ℕ → ℕ → ℕ → ℝ) (flat : Retained.UniformlyFlat (C := R.family) J eta)
    (s δ M c : ℝ) (hs : 0 ≤ s) (hs2 : s < 2) (hδ : 0 < δ) (hM : 0 ≤ M) (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop, ∀ datum : LocalFormal.Datum R.family Γ, datum.level = m →
      ∀ (F : AnalyticInput J A datum) (I : FullPreparedInputAt F (eta datum.cutoff datum.period datum.level)),
      I.regularPrice ≤ M * regulatorRun R.family datum.cutoff datum.period (datum.level+1)^(s+δ) →
        Retained.ordinaryRate K I 1 ≤ c * regulatorRun R.family datum.cutoff datum.period datum.level^s := by
  let T := (2:ℝ)^s
  let C := K.markedConstant 1 + J.inheritedConstant + 1
  have hT : 0 ≤ T := Real.rpow_nonneg (by norm_num) _
  have hC : 0 ≤ C := add_nonneg (add_nonneg (K.marked_constant_nonnegative 1 zero_lt_one)
      J.inherited_constant_nonnegative) zero_le_one
  obtain ⟨first, hCal⟩ := flat.2 3
  filter_upwards [eventually_ge_atTop first, K.eventually_markedRate_square hG R.makes,
    ActualRunAdjacentCoupling.eventually_ratio R hG,
    FundedSurplusPrice.cost_small R hG A (C*T) (mul_nonneg hC hT) 0
      (2-s) (c/2) (sub_pos.mpr hs2) (half_pos hc),
    ActualNumericGeometrySmallness.eventually_cost_geometry_coupling_small R hG A K
      (M*T) (mul_nonneg hM hT) 0 (c/2) (half_pos hc) δ hδ]
    with m hm fresh ratio smallFresh smallOld
  intro datum hlevel F I hprice
  subst m
  let m := datum.level
  let gf := regulatorRun R.family datum.cutoff datum.period (m+1)
  let gc := regulatorRun R.family datum.cutoff datum.period m
  have hf : 0 < gf := Currency.g_pos R.makes _ _ _ datum.below
  have hg : 0 < gc := Currency.g_pos R.makes _ _ _ datum.below.le
  have hK : 0 ≤ K.geometry m := K.geometry_nonnegative m
  have hcomp : gf^s ≤ T*gc^s :=
    (Real.rpow_le_rpow hf.le ((div_le_iff₀ hg).mp (ratio datum.cutoff datum.period datum.below).2) hs).trans_eq
      (Real.mul_rpow (by norm_num) hg.le)
  have hnew : markedRate J.order 1 (K.markedConstant 1) (K.geometry m) I.inherited
      (eta datum.cutoff datum.period m) gf ≤ C*gf^2 :=
    fresh datum.cutoff datum.period datum.below _ _ I.inherited_bound
      (hCal _ _ _ hm datum.below F.physical_period)
  have hfresh : C*T*gf^(2-s) ≤ c/2 := by
    simpa only [pow_zero,mul_one] using smallFresh datum.cutoff datum.period datum.below
  have hpay := transfer hf hg.le hC hcomp hfresh
  rw [show s+(2-s) = (2:ℝ) by ring, Real.rpow_two] at hpay
  have hrough : (K.geometry m*M)*T*gf^δ ≤ c/2 := by
    calc
      _ = (M*T)*A.admittedCost m^0 * K.geometry m*gf^δ := by simp only [pow_zero,mul_one]; ring
      _ ≤ _ := smallOld datum.cutoff datum.period datum.below
  have hgrowth : K.geometry m * I.regularPrice ≤ (c/2)*gc^s :=
    (mul_le_mul_of_nonneg_left hprice hK).trans
      ((show K.geometry m*(M*gf^(s+δ)) = (K.geometry m*M)*gf^(s+δ) by ring).le.trans
        (transfer hf hg.le (mul_nonneg hK hM) hcomp hrough))
  exact (add_le_add (hnew.trans hpay) hgrowth).trans_eq (show (c/2)*gc^s+(c/2)*gc^s = c*gc^s by ring)

/-- The zero starting regular price buys order one. Every finite successor
retains a positive half of the preceding ordinary exponent. -/
def order (n : ℕ) : ℝ := (1/2:ℝ)^n

theorem step (R : Run G) (hG : G.Simple) (J : Request V)
    (A : NumericSchedule R.family J) (K : NumericPrices A)
    (eta : ℕ → ℕ → ℕ → ℝ) (flat : Retained.UniformlyFlat (C := R.family) J eta) (n : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ datum : LocalFormal.Datum R.family Γ, datum.level = m →
      ∀ (F : AnalyticInput J A datum) (I : FullPreparedInputAt F (eta datum.cutoff datum.period datum.level)),
      I.regularPrice ≤ regulatorRun R.family datum.cutoff datum.period (datum.level+1)^(order n) →
        Retained.ordinaryRate K I 1 ≤ 1 ∧ Retained.ordinaryRate K I 1 ≤
          regulatorRun R.family datum.cutoff datum.period datum.level^(order (n+1)) := by
  have hp : 0 < order (n+1) := pow_pos (by norm_num) _
  have hle : order (n+1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hs : order (n+1) < 2 := hle.trans_lt (by norm_num)
  have he : order n = order (n+1)+order (n+1) := by simp only [order,pow_succ]; ring
  filter_upwards [price (Γ:=Γ) R hG J A K eta flat (order (n+1)) (order (n+1)) 1 1
    hp.le hs hp zero_le_one zero_lt_one, Currency.g_small hG R.makes 1 zero_lt_one]
    with m advance small
  intro datum hm F I hi
  subst m
  have h := advance datum rfl F I (by simpa only [one_mul,←he] using hi)
  rw [one_mul] at h
  have hg := Currency.g_pos R.makes datum.cutoff datum.period datum.level datum.below.le
  exact ⟨h.trans (Real.rpow_le_one hg.le (small datum.cutoff datum.period datum.below.le).le hp.le),h⟩

end YM.Integration.WilsonLimitConstruction.FundedOrdinaryReentry
end
