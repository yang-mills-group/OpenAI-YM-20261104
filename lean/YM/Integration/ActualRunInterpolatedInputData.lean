import YM.Integration.ActualRunInterpolatedPackets

/-! Exact data for the literal next-input packet. The occupied lower floor
is independent of the positive cap and the truncation order. The displayed
finite copy bill supplies a qualitative Paid receipt at every actual step;
the separate leading-one eventual bill remains the iteration estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunInterpolatedInputData

open Lattice Wilson RG Marker Precision
open PhysicalNext.Repeat.Legato Pert.Asymptotics MatchingLedger.Compass.Income
open Comparison.Density.RenderM LocalComparison
open ActualRunInterpolatedPackets ActualPacketInterpolatedRetuning
open ActualRunPacketRetuning ActualPacketFiniteCopies ActualPacketAdaptiveCopies
open ActualPacketCorrectedCoefficients ActualBetaRemainder
open ActualRunCouplingChart (betaDifference)
open scoped Classical

variable {G : Gauge} {side : Side} {V : Type} [DecidableEq V]
    {C : Census V} {D : V → ComparisonDensity.Address.Orbit}

/-- The actual finite coefficient sum, used only for qualitative admission. -/
def copyBill (R : Run G) (N period m : ℕ)
    (P : MarkedPackets D G side C) (r : ℕ) : ℝ :=
  coefficientMass P.powerCap (grid r)
    (normalizedCoefficient r (betaDifference R N period m)
      (regulatorRun R.family N period m))
    (regulatorRun R.family N period m)

/-- Copying preserves the strict occupied-row floor, even when B is zero.
No coupling positivity is needed for this structural assertion. -/
theorem onRun_floor (R : Run G) (N period m : ℕ)
    (P : MarkedPackets D G side C) (r B : ℕ)
    (hfloor : ∀ i T, P.packet i = some T → 0 < (B : ℤ) + P.power i) :
    ∀ k T, (onRun R N period m P r).packet k = some T →
      0 < (B : ℤ) + (onRun R N period m P r).power k := by
  let A := retune P (unit (betaDifference R N period m)
    (regulatorRun R.family N period m))
  let c := normalizedCoefficient r (betaDifference R N period m)
    (regulatorRun R.family N period m)
  intro k T hT
  change (adaptive A r c).packet k = some T at hT
  change 0 < (B : ℤ) + (adaptive A r c).power k
  by_cases hk : kept A r k
  · have hcopy : (copies A (grid r) c).packet k = some T := by
      simpa only [adaptive, if_pos hk] using hT
    obtain ⟨Q, hQ, _⟩ := Option.map_eq_some_iff.mp hcopy
    change (P.packet (index (grid r) k).1).map
      (scaleToken ((unit (betaDifference R N period m)
        (regulatorRun R.family N period m) : ℂ) ^
          P.power (index (grid r) k).1)) = some Q at hQ
    obtain ⟨U, hU, _⟩ := Option.map_eq_some_iff.mp hQ
    have hp : P.power (index (grid r) k).1 ≤ (adaptive A r c).power k :=
      original_power_le A r c k
    exact (hfloor _ U hU).trans_le (add_le_add_right hp (B : ℤ))
  · rw [inactive_absent A r c k hk] at hT
    cases hT

/-- The original fine Paid receipt gives an actual coarse Paid receipt
with its literal finite copy bill, before any asymptotic cost estimate. -/
theorem onRun_paid (R : Run G) (N period m : ℕ) (hm : m < N)
    (P : MarkedPackets D G side C) (r : ℕ)
    {p : BudgetPoint} {address : V → Support side}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) side}
    {w : V → ℝ} {width budget : ℝ} {offset slope : ℕ}
    (hP : P.Paid p address region w
      (regulatorRun R.family N period (m + 1)) width budget offset slope) :
    (onRun R N period m P r).Paid p address region w
      (regulatorRun R.family N period m) width
      (budget * copyBill R N period m P r) offset slope := by
  have hunit :
      unit (betaDifference R N period m) (regulatorRun R.family N period m) *
        regulatorRun R.family N period m =
          regulatorRun R.family N period (m + 1) := by
    change ActualRunCouplingChart.unit R N period m
      (regulatorRun R.family N period m) * regulatorRun R.family N period m = _
    rw [ActualRunCouplingChart.unit_coarse R N period m hm]
    exact div_mul_cancel₀ _
      (Weather.runs_pos R.family R.makes hm.le period).ne'
  have hpaid : P.Paid p address region w
      (unit (betaDifference R N period m) (regulatorRun R.family N period m) *
        regulatorRun R.family N period m) width budget offset slope := by
    rw [hunit]
    exact hP
  have hcopy := copies_paid
    (retune P (unit (betaDifference R N period m)
      (regulatorRun R.family N period m))) (grid r)
    (normalizedCoefficient r (betaDifference R N period m)
      (regulatorRun R.family N period m))
    (regulatorRun R.family N period m)
    (Weather.runs_pos R.family R.makes hm.le period).ne'
    (retune_paid P _ _ hpaid)
  exact adaptive_paid
    (retune P (unit (betaDifference R N period m)
      (regulatorRun R.family N period m))) r
    (normalizedCoefficient r (betaDifference R N period m)
      (regulatorRun R.family N period m)) hcopy

end YM.Integration.ActualRunInterpolatedInputData
end
