import YM.Integration.WilsonMeasuredWindingCalendar

/-! Ultraviolet-uniform summation of winding expenses with the physical period retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredWindingSum
open Filter Lattice RG PhysicalNext.Repeat.Legato ActualRunAdmissionScales
open scoped Topology BigOperators
variable {G : Gauge}

/-- Room for the downstream amplification, including a fixed power at every age. -/
def room (A : Levels G) (K : ℝ) (i : ℕ) : ℝ :=
  Real.exp (K*(1+A.S.scale i)*Real.log (2+A.clock.hatBeta i))

private theorem absorbed (A : Levels G) (simple : G.Simple) {K : ℝ} (hK : 0 ≤ K) :
    ∀ᶠ i : ℕ in atTop, 1 ≤ A.clock.hatBeta i ∧
      K*(1+A.S.scale i)*Real.log (2+A.clock.hatBeta i) ≤ (A.clock.hatBeta i)^3/2048 := by
  let C := K*(1+G.slopeConstant⁻¹)*3
  have b := G.slopeConstant_pos simple
  filter_upwards [(WardBin.bell A simple).eventually_ge_atTop (max 1 (2048*C))] with i hi
  let H := A.clock.hatBeta i
  have H₁ : 1 ≤ H := (le_max_left ..).trans hi
  have H₂ : 2048*C ≤ H := (le_max_right ..).trans hi
  have X : A.S.scale i ≤ G.slopeConstant⁻¹*H := by
    rw [← div_eq_inv_mul, le_div_iff₀ b]
    change _ ≤ A.clock.bar + G.slopeConstant*A.S.scale i
    linarith [A.clock.bar_pos]
  have factor : 1+A.S.scale i ≤ (1+G.slopeConstant⁻¹)*H := by linarith
  have logH : Real.log (2+H) ≤ 3*H :=
    (Real.log_le_self (by linarith)).trans (by linarith)
  have logpos : 0 ≤ Real.log (2+H) := Real.log_nonneg (by linarith)
  have hpos : 0 ≤ K*((1+G.slopeConstant⁻¹)*H) := by positivity
  refine ⟨H₁, ?_⟩
  calc _ ≤ (K*((1+G.slopeConstant⁻¹)*H))*(3*H) :=
         mul_le_mul (mul_le_mul_of_nonneg_left factor hK) logH logpos hpos
       _ = C*H^2 := by dsimp [C]; ring
       _ ≤ H^3/2048 := by nlinarith only [mul_le_mul_of_nonneg_right H₂ (sq_nonneg H)]

theorem invoice (R : Run G) (simple : G.Simple)
    (readout : RG05Preconstruction.ReadoutPurchase R.b) {K : ℝ} (hK : 0 ≤ K) :
    let A := R.family.path.levels
    ∀ᶠ m : ℕ in atTop, ∀ (j per : ℕ) (s : ℝ), 0 < s → s⁻¹ ≤ admittedCost A (m+j) →
      room A K (m+j)*Real.exp (-(s/512)*((R.family.side (m+j) per).val : ℝ)) ≤
      Real.exp (-((A.S.period per).val : ℝ)*(A.clock.hatBeta m)^2/2048)*(1/2 : ℝ)^j := by
  intro A
  obtain ⟨u,hu⟩ := eventually_atTop.1 (WilsonMeasuredWindingCalendar.width R simple readout)
  obtain ⟨v,hv⟩ := eventually_atTop.1 (absorbed A simple hK)
  filter_upwards [eventually_ge_atTop u, eventually_ge_atTop v, WilsonMeasuredWindingCalendar.square_rise A simple]
    with m mu mv rise j per s hs hc
  let P : ℝ := (A.S.period per).val
  let H := A.clock.hatBeta (m+j)
  let Hm := A.clock.hatBeta m
  have P₁ : 1 ≤ P := by
    change 1 ≤ ((A.S.period per).val : ℝ)
    exact_mod_cast Nat.succ_le_of_lt (A.S.period per).pos
  obtain ⟨H₁,small⟩ := hv (m+j) (by omega)
  have wind := hu (m+j) (by omega) s hs hc per
  have cubic : H^2 ≤ H^3 := by nlinarith only [mul_le_mul_of_nonneg_right H₁ (sq_nonneg H)]
  have base : H^3 ≤ P*H^3 := le_mul_of_one_le_left (by positivity) P₁
  have extra : P*H^2 ≤ P*H^3 := mul_le_mul_of_nonneg_left cubic (by positivity)
  have age : P*Hm^2 + 2048*(j : ℝ) ≤ P*H^2 := by
    have vj := le_mul_of_one_le_left (show 0 ≤ 2048*(j:ℝ) by positivity) P₁
    nlinarith only [vj, mul_le_mul_of_nonneg_left (rise j) (a := P) (by positivity)]
  have half : (1/2 : ℝ) = Real.exp (-Real.log 2) := by rw [Real.exp_neg,Real.exp_log (by norm_num)]; norm_num
  rw [room, half, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have log₂ : Real.log 2 ≤ 2 := Real.log_le_self (by norm_num)
  have jpos : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have final : 0 ≤ P * Hm^2 := by positivity
  change K*(1+A.S.scale (m+j))*Real.log (2+H) + _ ≤ -P*Hm^2/2048 + _
  change K*(1+A.S.scale (m+j))*Real.log (2+H) ≤ H^3/2048 at small
  change P*H^3 ≤ _ at wind
  nlinarith only [small,wind,extra,base,age,final,mul_le_mul_of_nonneg_left log₂ jpos]

private theorem half_sum (k : ℕ) : ∑ j ∈ Finset.range k, (1/2 : ℝ)^j ≤ 2 := by
  have eqn : (∑ j ∈ Finset.range k, (1/2 : ℝ)^j) + 2*(1/2 : ℝ)^k = 2 := by
    induction k with
    | zero => norm_num
    | succ k ih => rw [Finset.sum_range_succ, pow_succ]; linarith
  linarith [pow_nonneg (by norm_num : 0 ≤ (1/2 : ℝ)) k]

/-- All purchases precede the ultraviolet cutoff and physical period. -/
theorem all_dates (R : Run G) (simple : G.Simple)
    (readout : RG05Preconstruction.ReadoutPurchase R.b) {K : ℝ} (hK : 0 ≤ K) :
    let A := R.family.path.levels
    ∀ᶠ m : ℕ in atTop, ∀ (N per : ℕ) (payment : ℕ → ℝ),
      (∀ j < N-m, ∃ s : ℝ, 0 < s ∧ s⁻¹ ≤ admittedCost A (m+j) ∧
        payment (m+j) ≤ room A K (m+j)*Real.exp (-(s/512)*((R.family.side (m+j) per).val : ℝ))) →
      ∑ j ∈ Finset.range (N-m), payment (m+j) ≤
        2*Real.exp (-((A.S.period per).val : ℝ)*(A.clock.hatBeta m)^2/2048) := by
  intro A
  filter_upwards [invoice R simple readout hK] with m one N per payment priced
  let B := Real.exp (-((A.S.period per).val : ℝ)*(A.clock.hatBeta m)^2/2048)
  calc _ ≤ ∑ j ∈ Finset.range (N-m), B*(1/2 : ℝ)^j := by
         apply Finset.sum_le_sum
         intro j hj
         obtain ⟨s,hs,hc,h⟩ := priced j (Finset.mem_range.mp hj)
         exact h.trans (one j per s hs hc)
       _ = B * ∑ j ∈ Finset.range (N-m), (1/2 : ℝ)^j := (Finset.mul_sum ..).symm
       _ ≤ 2*B := by rw [mul_comm 2 B]; exact mul_le_mul_of_nonneg_left (half_sum _) (Real.exp_pos _).le

end YM.Integration.WilsonMeasuredWindingSum
