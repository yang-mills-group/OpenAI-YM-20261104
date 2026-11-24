import YM.Integration.OriginalPeriodWindingPrice

/-! Cumulative signed winding prices on the selected Wilson calendar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredWindingCalendar
open Filter Lattice RG PhysicalNext.Repeat.Legato
open ActualRunAdmissionScales ActualRunAdmissionClock
open scoped Topology BigOperators
variable {G : Gauge}

private theorem den_power (A : Levels G) (simple : G.Simple) (d : ℕ) :
    ∀ᶠ i : ℕ in atTop, A.clock.hatBeta i ^ d ≤ ((A.S.denominator i).val : ℝ) := by
  filter_upwards [OriginalPeriodWindingPrice.period_power A (d+1),
    (WardBin.bell A simple).eventually_ge_atTop ((A.S.period 0).val : ℝ)] with i pow large
  have h := pow 0
  rw [Schedule.side, PNat.mul_coe, Nat.cast_mul, pow_succ] at h
  apply le_of_mul_le_mul_left (a := ((A.S.period 0).val : ℝ)) _ (by positivity)
  calc _ ≤ A.clock.hatBeta i ^ d * A.clock.hatBeta i := by
         rw [mul_comm]; exact mul_le_mul_of_nonneg_left large (pow_nonneg (WardBin.hot A i).le _)
       _ ≤ _ := h

theorem width (R : Run G) (simple : G.Simple)
    (readout : RG05Preconstruction.ReadoutPurchase R.b) :
    let A := R.family.path.levels
    ∀ᶠ i : ℕ in atTop, ∀ s : ℝ, 0 < s → s⁻¹ ≤ admittedCost A i → ∀ per : ℕ,
      ((A.S.period per).val : ℝ) * (A.clock.hatBeta i)^3 ≤ s * ((R.family.side i per).val : ℝ) := by
  intro A
  have mesh := ActualRunQLocalAdmission.actual_preMesh R readout
  filter_upwards [cost_subpower R.family simple R.makes mesh 1 zero_lt_one,
    actual_inverse_lower R.family simple R.makes mesh, den_power A simple 4] with i cost band den s hs hs' per
  let g := Pert.Asymptotics.regulatorRun R.family (i+1) 0 (i+1)
  have hc : admittedCost A i ≤ g⁻¹ := by
    simpa only [Real.rpow_neg_one] using cost (i+1) 0 (Nat.lt_succ_self i)
  have hb : (A.clock.hatBeta i)⁻¹ ≤ g := band (i+1) 0 (Nat.lt_succ_self i)
  have hsg := inv_anti₀ (inv_pos.mpr hs) (hs'.trans hc)
  have hsH : (A.clock.hatBeta i)⁻¹ ≤ s := hb.trans (by simpa only [inv_inv] using hsg)
  have hot := WardBin.hot A i
  have lower : (A.clock.hatBeta i)^3 ≤ s * ((A.S.denominator i).val : ℝ) := by
    calc _ = (A.clock.hatBeta i)⁻¹ * (A.clock.hatBeta i)^4 := by field_simp [hot.ne']
         _ ≤ _ := mul_le_mul hsH den (pow_nonneg hot.le _) hs.le
  change _ ≤ s * ((A.S.side i per).val : ℝ)
  rw [Schedule.side, PNat.mul_coe, Nat.cast_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left lower (by positivity)

private theorem beta_step (A : Levels G) (simple : G.Simple) (i : ℕ) :
    A.clock.hatBeta i + G.slopeConstant * Real.log 3 ≤ A.clock.hatBeta (i+1) := by
  have hl : (3 : ℝ) ≤ (A.S.block i).val := by exact_mod_cast A.S.block_large i
  have h := mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) hl) (G.slopeConstant_pos simple).le
  change A.clock.bar + G.slopeConstant * A.S.scale i + _ ≤ A.clock.bar + G.slopeConstant * A.S.scale (i+1)
  rw [Schedule.scale_succ]
  linarith

theorem square_rise (A : Levels G) (simple : G.Simple) :
    ∀ᶠ m : ℕ in atTop, ∀ j : ℕ,
      (A.clock.hatBeta m)^2 + 2048*(j : ℝ) ≤ (A.clock.hatBeta (m+j))^2 := by
  let d := G.slopeConstant * Real.log 3
  have hd : 0 < d := mul_pos (G.slopeConstant_pos simple) (Real.log_pos (by norm_num))
  obtain ⟨m₀, hot⟩ := eventually_atTop.1 ((WardBin.bell A simple).eventually_ge_atTop (1024/d))
  filter_upwards [eventually_ge_atTop m₀] with m hm j
  induction j with
  | zero => simp
  | succ j ih =>
    have big : 1024 ≤ A.clock.hatBeta (m+j)*d := (div_le_iff₀ hd).mp (hot _ (by omega))
    have step : A.clock.hatBeta (m+j) + d ≤ A.clock.hatBeta (m+j+1) := beta_step A simple _
    have sq := pow_le_pow_left₀ (add_nonneg (WardBin.hot A _).le hd.le) step 2
    rw [Nat.cast_succ]
    change _ ≤ (A.clock.hatBeta (m+j+1))^2
    nlinarith [sq_nonneg d]

end YM.Integration.WilsonMeasuredWindingCalendar
