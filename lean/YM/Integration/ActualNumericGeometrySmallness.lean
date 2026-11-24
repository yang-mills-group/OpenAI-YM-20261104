import YM.Integration.FullQLocalNumericSchedule
import YM.Integration.ActualRunBetaResetDomain
import Mathlib.Tactic.FieldSimp

/-! Uniform cost-and-geometry smallness for every positive real coupling power.
The actual Run and both original subpower receipts are unchanged. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualNumericGeometrySmallness
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

/-- Every fixed cost power and the original geometry price are paid by
any positive power of the actual fine regulator, on one tail before the
cutoff and period are chosen. -/
theorem eventually_cost_geometry_coupling_small {G : Gauge} {V : Type}
    (R : Run G) (hG : G.Simple) {J : Request V}
    (A : NumericSchedule R.family J) (K : NumericPrices A)
    (C : ℝ) (hC : 0 ≤ C) (d : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (a : ℝ) (ha : 0 < a) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      C * A.admittedCost m ^ d * K.geometry m *
        regulatorRun R.family N period (m + 1) ^ a ≤ epsilon := by
  let e := a / (2 * ((d : ℝ) + 1))
  have he : 0 < e := by dsimp only [e]; positivity
  obtain ⟨startA, hA⟩ := A.cost_subpower e he
  obtain ⟨startK, hK⟩ := K.subpower e he
  have hC1 : 0 < C + 1 := by linarith
  let eta := (epsilon / (C + 1)) ^ (2 / a)
  have heta : 0 < eta :=
    Real.rpow_pos_of_pos (div_pos hepsilon hC1) _
  have hexponent : (-e * (d : ℝ) + -e) + a = a / 2 := by
    have hd1 : (d : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
    dsimp only [e]
    field_simp [hd1]
    ring
  have heta_power : eta ^ (a / 2) = epsilon / (C + 1) := by
    have hexp : (2 / a) * (a / 2) = (1 : ℝ) := by
      field_simp [ha.ne']
    dsimp only [eta]
    rw [← Real.rpow_mul (div_pos hepsilon hC1).le, hexp, Real.rpow_one]
  filter_upwards [eventually_ge_atTop startA, eventually_ge_atTop startK,
    fine_small R hG eta heta] with m hmA hmK hsmall
  intro N period hN
  let g := regulatorRun R.family N period (m + 1)
  have hg : 0 < g :=
    Weather.runs_pos R.family R.makes (Nat.succ_le_of_lt hN) period
  have hcost : A.admittedCost m ^ d ≤ g ^ (-e * (d : ℝ)) := by
    calc
      _ ≤ (g ^ (-e)) ^ d :=
        pow_le_pow_left₀ (A.admitted_cost_nonnegative m) (hA m hmA N period hN) d
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hg.le]
  have hgeometry : K.geometry m ≤ g ^ (-e) := hK m hmK N period hN
  have hproduct : A.admittedCost m ^ d * K.geometry m ≤
      g ^ (-e * (d : ℝ)) * g ^ (-e) :=
    mul_le_mul hcost hgeometry (K.geometry_nonnegative m) (Real.rpow_nonneg hg.le _)
  have hsmallpower : g ^ (a / 2) ≤ epsilon / (C + 1) :=
    (Real.rpow_le_rpow hg.le (hsmall N period hN) (by positivity)).trans_eq heta_power
  calc
    C * A.admittedCost m ^ d * K.geometry m * g ^ a =
        C * (A.admittedCost m ^ d * K.geometry m) * g ^ a := by ring
    _ ≤ C * (g ^ (-e * (d : ℝ)) * g ^ (-e)) * g ^ a :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hproduct hC)
        (Real.rpow_nonneg hg.le _)
    _ = C * g ^ (a / 2) := by
      rw [mul_assoc, ← Real.rpow_add hg, ← Real.rpow_add hg, hexponent]
    _ ≤ (C + 1) * g ^ (a / 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hg.le _)
    _ ≤ (C + 1) * (epsilon / (C + 1)) :=
      mul_le_mul_of_nonneg_left hsmallpower hC1.le
    _ = epsilon := (mul_comm _ _).trans (div_mul_cancel₀ _ hC1.ne')

end YM.Integration.ActualNumericGeometrySmallness
end
