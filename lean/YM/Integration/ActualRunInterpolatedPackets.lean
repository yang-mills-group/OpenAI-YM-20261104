import YM.Integration.ActualPacketInterpolatedRetuning
import YM.Integration.ActualRunBetaResetSmall

/-!
The corrected packet on the actual adjacent couplings of one retained Run.
The exact physical identity uses both original positive betas. Its normalized
copy bill is eventually at most 1+epsilon before every cutoff, period,
truncation order, packet layout, field, and test tuple. This is a native Paid
receipt; it asserts neither a RelativeBudget nor next-input admissibility.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunInterpolatedPackets
open Lattice Wilson RG Marker Precision Filter
open PhysicalNext.Repeat.Legato Pert.Asymptotics MatchingLedger.Compass.Income
open LocalComparison ActualPacketInterpolatedRetuning ActualRunPacketRetuning
open ActualPacketAdaptiveCopies ActualPacketCorrectedCoefficients ActualBetaRemainder
open ActualRunCouplingChart (betaDifference)
open scoped BigOperators Topology

variable {G : Gauge} {n : Side} {V : Type}
    {D : V → ComparisonDensity.Address.Orbit}
    [DecidableEq V] {S : Census V}

def onRun (R : Run G) (N period m : ℕ)
    (P : MarkedPackets D G n S) (r : ℕ) : MarkedPackets D G n S :=
  interpolated P r (betaDifference R N period m) (regulatorRun R.family N period m)

private theorem actual_domain (R : Run G) (N period m : ℕ) (hm : m < N) :
    0 < 1 - betaDifference R N period m *
      regulatorRun R.family N period m ^ 2 := by
  change 0 < ActualRunCouplingChart.radicand R N period m
    (regulatorRun R.family N period m)
  rw [ActualRunCouplingChart.coarse_radicand R N period m hm]
  exact div_pos
    (Weather.iceborn R.family R.makes (Nat.succ_le_of_lt hm) period)
    (Weather.iceborn R.family R.makes hm.le period)

private theorem actual_unit_mul (R : Run G) (N period m : ℕ) (hm : m < N) :
    unit (betaDifference R N period m) (regulatorRun R.family N period m) *
      regulatorRun R.family N period m =
        regulatorRun R.family N period (m + 1) := by
  change ActualRunCouplingChart.unit R N period m
    (regulatorRun R.family N period m) * regulatorRun R.family N period m = _
  rw [ActualRunCouplingChart.unit_coarse R N period m hm]
  exact div_mul_cancel₀ _
    (Weather.runs_pos R.family R.makes hm.le period).ne'

/-- Exact same-Run physical equality on the same full fields and all
independent test functions. No chosen inverse-function neighborhood is used. -/
theorem onRun_read [Fintype V] (R : Run G) (N period m : ℕ) (hm : m < N)
    (P : MarkedPackets D G n S) (r : ℕ)
    {B : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {width budget : ℝ} {offset slope : ℕ}
    (hP : P.Paid B address region w (regulatorRun R.family N period (m + 1))
      width budget offset slope) (x : TestSpace D) (U : Config G n) :
    (onRun R N period m P r).read x (regulatorRun R.family N period m) U =
      P.read x (regulatorRun R.family N period (m + 1)) U := by
  have hPin : P.Paid B address region w
      (unit (betaDifference R N period m) (regulatorRun R.family N period m) *
        regulatorRun R.family N period m) width budget offset slope := by
    rw [actual_unit_mul R N period m hm]
    exact hP
  unfold onRun
  rw [interpolated_at_physical P r _ _
    (Weather.runs_pos R.family R.makes hm.le period).ne'
    (actual_domain R N period m hm) hPin x U, actual_unit_mul R N period m hm]

/-- The normalized bill tends to one uniformly before all cutoffs, periods,
signed powers in the fixed cap, and row-dependent truncation orders. -/
theorem normalized_bill_eventually (cap : ℕ) (R : Run G) (hG : G.Simple)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      ∀ e : ℤ, |e| ≤ (cap : ℤ) → ∀ r : ℕ,
        (∑ j : Fin (grid r + 1),
          ‖normalizedCoefficient r (betaDifference R N period m)
            (regulatorRun R.family N period m) e j‖ *
              ‖(regulatorRun R.family N period m : ℂ) ^ (2 * j.val)‖) ≤ 1 + ε := by
  let C := paymentConstant cap
  have hC : 0 < C := paymentConstant_pos cap
  have hη : 0 < min (1 / 2 : ℝ) (ε / C) :=
    lt_min (by norm_num) (div_pos hε hC)
  filter_upwards [ActualRunBetaResetSmall.eventually_small R hG hη] with m hm
  intro N period hN e he r
  have hs : |betaDifference R N period m *
      regulatorRun R.family N period m ^ 2| ≤ min (1 / 2 : ℝ) (ε / C) :=
    hm N period hN
  have hbound := (Classical.choose_spec (normalized_uniform_bill cap)).2
    e he (betaDifference R N period m) (regulatorRun R.family N period m)
    (Weather.runs_pos R.family R.makes hN.le period).ne'
    (hs.trans (min_le_left _ _)) r
  have hmul := mul_le_mul_of_nonneg_left
    (hs.trans (min_le_right _ _)) hC.le
  have hcancel : C * (ε / C) = ε := by
    rw [mul_comm C, div_mul_cancel₀ _ hC.ne']
  change _ ≤ 1 + C * _ at hbound
  linarith

/-- One actual tail works before every packet side, test family, cutoff,
period and requested order. Every native Paid field is transferred with
the same width/cover data and the complete budget multiplier 1+epsilon. -/
theorem onRun_paid_eventually (cap : ℕ) (R : Run G) (hG : G.Simple)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      ∀ {n' : Side} {V' : Type} [DecidableEq V']
        {D' : V' → ComparisonDensity.Address.Orbit} {S' : Census V'}
        (P : MarkedPackets D' G n' S'), P.powerCap ≤ cap → ∀ r : ℕ,
        ∀ {B : BudgetPoint} {address : V' → Support n'}
          {region : Comparison.Density.Testing.Region (fun v => (D' v).Mood) n'}
          {w : V' → ℝ} {width budget : ℝ} {offset slope : ℕ},
          P.Paid B address region w (regulatorRun R.family N period (m + 1))
            width budget offset slope →
          (onRun R N period m P r).Paid B address region w
            (regulatorRun R.family N period m) width (budget * (1 + ε))
              offset slope := by
  filter_upwards [normalized_bill_eventually cap R hG hε] with m hm
  intro N period hN n' V' instV D' S' P hcap r B address region w width budget
    offset slope hP
  have hPin : P.Paid B address region w
      (unit (betaDifference R N period m) (regulatorRun R.family N period m) *
        regulatorRun R.family N period m) width budget offset slope := by
    rw [actual_unit_mul R N period m hN]
    exact hP
  apply adaptive_paid_of_bound _ r _ _
    (Weather.runs_pos R.family R.makes hN.le period).ne'
    (1 + ε) (by linarith) _ (retune_paid P _ _ hPin)
  intro e he
  exact hm N period hN e (he.trans (by exact_mod_cast hcap)) r

end YM.Integration.ActualRunInterpolatedPackets
end
