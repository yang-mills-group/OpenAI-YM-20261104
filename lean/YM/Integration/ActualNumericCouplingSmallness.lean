import YM.Integration.FullQLocalNumericSchedule
import YM.Integration.ActualRunBetaResetDomain

/-! Every fixed polynomial in the original numerical bill is paid by two
powers of the actual fine regulator. All level tails precede N and period.
The proof uses only the original subpower receipt and actual Weather band. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualNumericCouplingSmallness
open Filter RG PhysicalNext.Repeat.Legato Pert.Asymptotics
open FullQLocal.RenderedStep MatchingLedger.Compass.Income
open scoped Topology

private theorem fine_small {G : Gauge} (R : Run G) (hG : G.Simple)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      regulatorRun R.family N period (m + 1) ≤ eta := by
  let D := R.family.path.levels
  have ht := (WardBin.bell D hG).comp (tendsto_add_atTop_nat 1)
  filter_upwards [ht.eventually_ge_atTop ((2 / eta) ^ 2)] with m hm
  intro N period hN
  have hb := WardBin.hot D (m + 1)
  have hs : (2 / eta : ℝ) ≤ Real.sqrt (D.clock.hatBeta (m + 1)) :=
    (Real.le_sqrt (div_nonneg (by norm_num) heta.le) hb.le).2 hm
  have hband := (Weather.into_band R.family R.makes
    (Nat.succ_le_of_lt hN) period).2
  calc
    regulatorRun R.family N period (m + 1) ≤
        2 * (Real.sqrt (D.clock.hatBeta (m + 1)))⁻¹ := hband
    _ = 2 / Real.sqrt (D.clock.hatBeta (m + 1)) :=
      (div_eq_mul_inv _ _).symm
    _ ≤ eta := (div_le_iff₀ (Real.sqrt_pos.mpr hb)).2
      (by nlinarith only [(div_le_iff₀ heta).mp hs])

/-- One original level tail pays every fixed numerical cost polynomial,
uniformly before the fine cutoff and physical period are selected. -/
theorem eventually_cost_coupling_small {G : Gauge} {V : Type}
    (R : Run G) (hG : G.Simple) {J : Request V}
    (A : NumericSchedule R.family J) (C : ℝ) (hC : 0 ≤ C)
    (d : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      C * A.admittedCost m ^ d *
        regulatorRun R.family N period (m + 1) ^ 2 ≤ epsilon := by
  have hq : 0 < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos d
  obtain ⟨start, hstart⟩ := A.cost_subpower
    (1 / ((d + 1 : ℕ) : ℝ)) (div_pos zero_lt_one hq)
  have hC1 : 0 < C + 1 := by linarith
  filter_upwards [eventually_ge_atTop start,
    fine_small R hG (epsilon / (C + 1)) (div_pos hepsilon hC1)] with m hm hsmall
  intro N period hN
  let g := regulatorRun R.family N period (m + 1)
  have hg : 0 < g := Weather.runs_pos R.family R.makes
    (Nat.succ_le_of_lt hN) period
  have hpower := pow_le_pow_left₀ (A.admitted_cost_nonnegative m)
    (hstart m hm N period hN) (d + 1)
  have hexponent :
      -(1 / ((d + 1 : ℕ) : ℝ)) * ((d + 1 : ℕ) : ℝ) = (-1 : ℝ) := by
    rw [neg_mul, div_mul_cancel₀ _ hq.ne']
  have hrpow :
      (g ^ (-(1 / ((d + 1 : ℕ) : ℝ)))) ^ (d + 1) = g⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hg.le, hexponent, Real.rpow_neg_one]
  have htop : A.admittedCost m ^ (d + 1) ≤ g⁻¹ := hpower.trans_eq hrpow
  have hdom : A.admittedCost m ^ d ≤ g⁻¹ := by
    calc
      _ = A.admittedCost m ^ d * 1 := (mul_one _).symm
      _ ≤ A.admittedCost m ^ d * A.admittedCost m :=
        mul_le_mul_of_nonneg_left (A.admitted_cost_ge_one m)
          (pow_nonneg (A.admitted_cost_nonnegative m) _)
      _ = A.admittedCost m ^ (d + 1) := (pow_succ _ _).symm
      _ ≤ g⁻¹ := htop
  calc
    C * A.admittedCost m ^ d * g ^ 2 ≤ C * g⁻¹ * g ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdom hC) (sq_nonneg g)
    _ = C * g := by rw [mul_assoc, pow_two, inv_mul_cancel_left₀ hg.ne']
    _ ≤ (C + 1) * g := mul_le_mul_of_nonneg_right (by linarith) hg.le
    _ ≤ (C + 1) * (epsilon / (C + 1)) :=
      mul_le_mul_of_nonneg_left (hsmall N period hN) hC1.le
    _ = epsilon := (mul_comm _ _).trans (div_mul_cancel₀ _ hC1.ne')

end YM.Integration.ActualNumericCouplingSmallness
end
