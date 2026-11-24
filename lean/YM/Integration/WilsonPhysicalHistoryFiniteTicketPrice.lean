import YM.Next.WARD_BIN.Hats
import YM.Integration.WilsonPhysicalHistoryFiniteTicket

/-! Uniform payment of a polynomial divided bill for a fixed census on the
actual levels of a Wilson trajectory. The location and period do not enter. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryFiniteTicketPrice
open Filter Real Lattice Wilson RG Source
open scoped Topology
variable {G : Gauge} (T : Levels G) (simple : G.Simple)

include simple in
theorem all_late (names p h : ℕ) {C ε : ℝ} (hc : 0 ≤ C) (he : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ i, k ≤ i → ∀ Θ : ℝ, Θ ≤ C * (T.clock.hatCoupling i)⁻¹^h →
      T.clock.forcedAllowance i + names * (Θ*sqrt (T.clock.forcedAllowance i)) ≤
        ε*(T.clock.hatCoupling i)^p := by
  let coeff : ℝ := 1 + (names : ℝ) * C
  have hc' : 0 ≤ coeff := add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) hc)
  have vanish : Tendsto (fun i => coeff * ((T.clock.hatCoupling i)⁻¹^(p+h) *
      sqrt (T.clock.forcedAllowance i))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (WardBin.pale T simple (p+h)).const_mul coeff
  obtain ⟨start, after⟩ := eventually_atTop.1 (vanish.eventually (ge_mem_nhds he))
  filter_upwards [eventually_ge_atTop start] with k hk
  intro i hki Θ bounded
  let g := T.clock.hatCoupling i
  let κ := sqrt (T.clock.forcedAllowance i)
  have gp : 0 < g := WardBin.stepG T i
  have one : 1 ≤ g⁻¹ := by
    change 1 ≤ ((sqrt (T.clock.hatBeta i))⁻¹)⁻¹
    rw [inv_inv]
    exact one_le_sqrt.mpr (T.fits.delayed i).le
  have kp : 0 ≤ κ := sqrt_nonneg _
  have low : κ ≤ 1 := sqrt_le_one.mpr (exp_le_one_iff.mpr
    (neg_nonpos.mpr (rpow_nonneg (exp_nonneg _) _)))
  have refund : T.clock.forcedAllowance i ≤ κ :=
    (mul_self_sqrt (WardBin.force_pos T i).le).symm.trans_le
      ((mul_le_mul_of_nonneg_left low kp).trans_eq (mul_one _))
  have gold : 1 ≤ g⁻¹^h := one_le_pow₀ one
  have pay : T.clock.forcedAllowance i + (names : ℝ)*(Θ*κ) ≤ coeff*g⁻¹^h*κ := by
    calc
      _ ≤ κ + (names:ℝ)*((C*g⁻¹^h)*κ) :=
        add_le_add refund (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right bounded kp) (Nat.cast_nonneg names))
      _ ≤ g⁻¹^h*κ + (names:ℝ)*((C*g⁻¹^h)*κ) :=
        add_le_add (by simpa only [one_mul] using mul_le_mul_of_nonneg_right gold kp) le_rfl
      _ = _ := by dsimp [coeff]; ring
  have field : coeff*g⁻¹^h*κ = (coeff*(g⁻¹^(p+h)*κ))*g^p := by
    rw [pow_add,inv_pow,inv_pow]
    field_simp [gp.ne']
  exact pay.trans (field.trans_le (mul_le_mul_of_nonneg_right (after i (hk.trans hki)) (pow_nonneg gp.le p)))

end YM.Integration.WilsonPhysicalHistoryFiniteTicketPrice
end

