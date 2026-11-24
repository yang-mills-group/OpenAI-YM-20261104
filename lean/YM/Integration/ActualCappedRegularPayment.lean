import YM.Integration.CappedRegularGrowth
import YM.Integration.ActualRunQLocalAdmission
import YM.IterationFour.Kinetic

/-! The original readout purchase pays the explicit capped regular bill.
The fixed orders/support precede the stage; the event precedes all physical
paths and bounded source prices. No profile-width upper bound is used. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualCappedRegularPayment
open Filter Lattice Wilson RG PhysicalNext.Repeat.Legato
open ActualRunAdmissionScales ActualRunAdmissionClock
open scoped Topology BigOperators
variable {G : Gauge}

/-- The original normalized path metric already bounds its direct term. -/
theorem direct_le_one {P : PathData G} {c : Clip} {σ C Λ : ℝ}
    (h : P.Bounds c σ C Λ) : c.direct ≤ 1 := by
  let i : PlaqAxes := ⟨(0, 1), by decide⟩
  have he := h.metric i i
  simp only [if_true] at he
  have hn : 0 ≤ ∑ k, P.symbol0 k i * P.symbol0 k i :=
    Finset.sum_nonneg fun k _ => mul_self_nonneg _
  linarith

/-- Any fixed polynomial in the proved native Admission cost is paid by
one power of the same family's original kinetic quote. -/
theorem polynomial_price (C : Family G) (hG : G.Simple)
    (hMesh : PreMesh C.path.levels) (K : ℝ) (hK : 0 ≤ K) (k : ℕ) :
    ∀ᶠ m in atTop, K * admittedCost C.path.levels m ^ k ≤
      IterationFour.Kinetic.price C m := by
  let A := C.path.levels
  have ht := ((LocalComparison.JetNormalization.monitor_hat_tendsto A hG k 2
    (by norm_num)).comp (tendsto_add_atTop_nat 1)).const_mul (K * (25 : ℝ)^k)
  rw [mul_zero] at ht
  filter_upwards [ht.eventually_le_const zero_lt_one,
    cost_monitor A hG hMesh, adjacent_beta A hG hMesh] with m hm hc hb
  have ha : 0 ≤ admittedCost A m := zero_le_one.trans (admittedCost_one A m)
  have hp : K * admittedCost A m ^ k * A.clock.hatCoupling (m+1)^2 ≤ 1 := by
    calc
      _ ≤ K * (25 * A.clock.monitor (m+1))^k * A.clock.hatCoupling (m+1)^2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hc k) hK) (sq_nonneg _)
      _ = (K * (25 : ℝ)^k) *
          (A.clock.monitor (m+1)^k * A.clock.hatCoupling (m+1)^2) := by
        rw [mul_pow]
        ring
      _ ≤ 1 := by simpa only [Function.comp_apply, Real.rpow_two] using hm
  have hβ : 0 < A.clock.hatBeta (m+1) := WardBin.hot A (m+1)
  have hi : A.clock.hatCoupling (m+1)^2 * A.clock.hatBeta (m+1) = 1 := by
    unfold Calendar.hatCoupling
    rw [inv_pow, Real.sq_sqrt hβ.le]
    exact inv_mul_cancel₀ hβ.ne'
  have hpaid := mul_le_mul_of_nonneg_right hp hβ.le
  rw [mul_assoc, hi, mul_one, one_mul] at hpaid
  exact hpaid.trans (hb.trans (IterationFour.Kinetic.two_hat_le C m))

private lemma profile_cost (A : Levels G) (m : ℕ) :
    (A.params m).width⁻¹ ≤ admittedCost A m ∧
      (A.params m).paths ≤ admittedCost A m := by
  have hp := inv_pos.mpr (pairWidth_pos A m)
  have hw := inv_anti₀ (pairWidth_pos A m)
    (show pairWidth A m ≤ (A.params m).width from min_le_right _ _)
  have hgeo := geometryCost_nonneg A m
  have hu := unitCost_nonneg A m
  have hbase : (pairWidth A m)⁻¹ ≤ admittedCost A m := by
    unfold admittedCost
    linarith
  refine ⟨hw.trans hbase, ?_⟩
  apply le_trans ?_ (cost_covers_geometry A m)
  have hpf := (A.params (m+1)).paths_pos
  have hc := (A.params m).columns_ge
  have hcf := (A.params (m+1)).columns_ge
  have hr := (A.params m).clip.radius_pos
  have hrf := (A.params (m+1)).clip.radius_pos
  have hm : 0 < A.clock.monitor m := Real.exp_pos _
  have hmf : 0 < A.clock.monitor (m+1) := Real.exp_pos _
  have hl := Real.rpow_nonneg hm.le (A.clock.theta (A.clock.J m))
  have hlf := Real.rpow_nonneg hmf.le (A.clock.theta (A.clock.J (m+1)))
  unfold geometryCost Calendar.loopCap
  linarith [Nat.cast_nonneg (α := ℝ) (A.clock.coverSize m),
    Nat.cast_nonneg (α := ℝ) (A.clock.coverSize (m+1))]

/-- Exact actual profile widths and path costs; only the requested norm
orders/support are fixed. The original path supplies direct≤1 internally. -/
theorem regular_price (R : Run G) (hG : G.Simple)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (q d : ℕ) (s : ℝ) (hq : 6 ≤ q) (hd : 2 ≤ d) (hs : 0 < s)
    (H₀ : ℝ) (hH₀ : 0 ≤ H₀) :
    ∀ᶠ m in atTop, ∀ (P : PathData G) (Λ H : ℝ),
      P.Bounds (R.family.path.levels.params m).clip
        (R.family.path.levels.params m).width
        (R.family.path.levels.params m).paths Λ →
      0 ≤ H → H ≤ H₀ →
      CappedRegularReset.regularNeed G
        (requestedBudget R.family.path.levels m q d s hq hd hs)
        (R.family.path.levels.params m).clip
        (R.family.path.levels.params m).width
        (R.family.path.levels.params m).paths 0 H ≤
      IterationFour.Kinetic.price R.family m := by
  let A := R.family.path.levels
  let p₀ := requestedBudget A 0 q d s hq hd hs
  let D := CappedRegularGrowth.degree p₀
  let K := 2 * CappedRegularGrowth.coefficient G p₀ * (3 : ℝ)^D * H₀
  have hcoef := CappedRegularGrowth.coefficient_positive G p₀
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  filter_upwards [polynomial_price R.family hG
    (ActualRunQLocalAdmission.actual_preMesh R hReadout) K hK (D+2)] with m hm P Λ H hP hH hHH
  let a := admittedCost A m
  have ha1 : 1 ≤ a := admittedCost_one A m
  have ha : 0 ≤ a := zero_le_one.trans ha1
  obtain ⟨hw, hc⟩ := profile_cost A m
  have hw0 := inv_pos.mpr (A.params m).width_pos
  have hc0 := (A.params m).paths_pos
  have hw' : 1 + 2 * (A.params m).width⁻¹ ≤ 3*a := by
    change (A.params m).width⁻¹ ≤ a at hw
    linarith
  have hc' : 1 + (A.params m).paths^2 ≤ 2*a^2 := by
    have hsq := pow_le_pow_left₀ hc0.le hc 2
    have ha2 : 1 ≤ a^2 := one_le_pow₀ ha1
    change (A.params m).paths^2 ≤ a^2 at hsq
    linarith
  have he := CappedRegularGrowth.regular_fields G
    (requestedBudget A m q d s hq hd hs) p₀ (A.params m).clip
    (A.params m).width (A.params m).paths H rfl rfl rfl
  change CappedRegularReset.regularNeed G (requestedBudget A m q d s hq hd hs)
    (A.params m).clip (A.params m).width (A.params m).paths 0 H ≤ _
  rw [he]
  calc
    _ ≤ CappedRegularGrowth.coefficient G p₀ *
        (1 + 2 * (A.params m).width⁻¹)^D * (1 + (A.params m).paths^2) * H :=
      CappedRegularGrowth.regular_growth G p₀ (A.params m).clip
        (A.params m).width_pos hc0.le hH (direct_le_one hP)
    _ ≤ CappedRegularGrowth.coefficient G p₀ * (3*a)^D * (2*a^2) * H₀ := by
      apply mul_le_mul ?_ hHH hH (by positivity)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hw' D) hcoef.le)
        hc' (by positivity) (by positivity)
    _ = K * a^(D+2) := by
      dsimp only [K]
      rw [mul_pow, pow_add]
      ring
    _ ≤ _ := hm

end YM.Integration.ActualCappedRegularPayment
end
