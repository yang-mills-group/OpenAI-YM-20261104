import YM.Integration.ActualRunInterpolatedInputData
import YM.Integration.NativePaidPacketColorsAt

/-! The fixed-order Colors of the literal next packet on one retained Run.
The original fine Paid receipt supplies the next packet's payment and floor.
The same supplied vacuum carries the explicit analytic and symmetry receipts. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunInterpolatedInput

open Lattice Wilson RG Marker Precision
open PhysicalNext.Repeat.Legato Pert.Asymptotics MatchingLedger.Compass.Income
open Comparison.Density.RenderM LocalComparison
open Comparison.RG02 Comparison.RG02.Assembly
open ActualRunInterpolatedPackets

variable {G : Gauge} {side : Side} {V : Type} [DecidableEq V] [Fintype V]
    {C : Census V} {D : V → ComparisonDensity.Address.Orbit}

/-- The literal fixed-B mark of the actual next packet and the same vacuum. -/
def colors (R : Run G) (N period m : ℕ)
    (P : MarkedPackets D G side C) (r B : ℕ)
    (newVac : ℝ → Config G side → ℝ) (x : TestSpace D) : Bulk.Colors C G side :=
  NativePaidPacketColorsAt.colorsAt (onRun R N period m P r) B newVac x

/-- Actual payment and the preserved occupied floor give the full input contract. -/
theorem input_colors (R : Run G) (N period m : ℕ) (hm : m < N)
    (P : MarkedPackets D G side C) (r B : ℕ)
    (hfloor : ∀ i T, P.packet i = some T → 0 < (B : ℤ) + P.power i)
    {p : BudgetPoint} {address : V → Support side}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) side}
    {w : V → ℝ} {width budget : ℝ} {offset slope : ℕ}
    (hP : P.Paid p address region w
      (regulatorRun R.family N period (m + 1)) width budget offset slope)
    (newVac : ℝ → Config G side → ℝ)
    (hv : GradeAt 3 (Bulk.projected newVac))
    (hG : ∀ g, GaugeInvariant (newVac g))
    (hE : ∀ g, Envelope (newVac g)) :
    InputColors (colors R N period m P r B newVac) (onRun R N period m P r) := by
  exact NativePaidPacketColorsAt.input_colorsAt
    (ActualRunInterpolatedInputData.onRun_paid R N period m hm P r hP) B
    (ActualRunInterpolatedInputData.onRun_floor R N period m P r B hfloor)
    (Weather.runs_pos R.family R.makes hm.le period).ne' newVac hv hG hE

/-- At the actual coarse coupling the entire marked log reads the original
fine packet on the same full configuration and independent test tuple. -/
theorem markedLog_coarse (R : Run G) (N period m : ℕ) (hm : m < N)
    (P : MarkedPackets D G side C) (r B : ℕ)
    {p : BudgetPoint} {address : V → Support side}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) side}
    {w : V → ℝ} {width budget : ℝ} {offset slope : ℕ}
    (hP : P.Paid p address region w
      (regulatorRun R.family N period (m + 1)) width budget offset slope)
    (newVac : ℝ → Config G side → ℝ) (x : TestSpace D) (U : Config G side) :
    Integral.markedLog (regulatorRun R.family N period m) U
      (colors R N period m P r B newVac x) =
        P.read x (regulatorRun R.family N period (m + 1)) U := by
  exact (NativePaidPacketColorsAt.colorsAt_markedLog
    (ActualRunInterpolatedInputData.onRun_paid R N period m hm P r hP) B
    (Weather.runs_pos R.family R.makes hm.le period).ne'
    newVac x (regulatorRun R.family N period m)
    (Weather.runs_pos R.family R.makes hm.le period).ne' U).trans
      (onRun_read R N period m hm P r hP x U)

end YM.Integration.ActualRunInterpolatedInput
end
