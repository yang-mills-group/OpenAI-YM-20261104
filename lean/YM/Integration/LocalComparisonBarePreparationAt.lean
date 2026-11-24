import YM.Integration.LocalComparisonFullPreparationAt
import YM.Integration.LocalComparisonVacuumRemainder

/-!
Pure marked preparation at an explicit requested norm. The auxiliary
remainder retains every original vacuum-gas row and the declared layout.
Its marked coefficients are zero, so the native zero-majorant constructor
works at any q. No nonzero-row norm upgrade is claimed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.LocalComparison.Global
open Lattice Wilson RG Marker
open RG3.Script.Picnic

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {C : Family G} {D : V → ComparisonDensity.Address.Orbit}

/-- A genuine full bare factorization has a zero-marked remainder at q,
with the same vacuum gas, fields, roots and complete independent tests. -/
def PreparedWithRemainderAt.of_bare_factorization
    (N period level : ℕ) (q : BudgetPoint) (Q : StepCarrier C N period level)
    (roots : V → Site (C.side level period))
    (input : Taste (TestSpace D) roots Q.rep R)
    (colors : TestSpace D → Comparison.RG02.Bulk.Colors R G (C.side level period))
    (packets : MarkedPackets D G (C.side level period) R)
    (w : V → ℝ) (kernelEnvelope : R.Mode → ℝ)
    (x₀ : TestSpace D) (hLayout : (input.leaf x₀).Active)
    (hColors : InputColors colors packets)
    (hw : ∀ v, 0 < w v) (hEnvelope : ∀ s, 0 < kernelEnvelope s)
    (hQuiet : kernelEnvelope R.quiet = 1)
    (hGas : ∀ U : Config G (C.side level period),
      Summable (fun s : Finset ℕ => ‖Q.rep.activities.gasOccurrence Q.rep.p s U‖))
    (hFactor : ∀ (x : TestSpace D) (U : Config G (C.side level period)),
      (input.leaf x).density U = (Q.rep.eval U : ℂ) •
        Poly.pass (packets.read x (Pert.Asymptotics.regulatorRun C N period level) U)) :
    PreparedWithRemainderAt N period level q Q roots input colors packets
      w kernelEnvelope 0 0 where
  convention := hColors
  remainder := vacuumRemainder input
  full x U := by
    rw [vacuumRemainder_density input x U (hGas U)]
    simpa only [mul_smul_comm, mul_one] using hFactor x U
  remainder_price := by
    have hκ : 0 < forcedDivisor C level := by
      change 0 < Real.sqrt (Real.exp _)
      exact Real.sqrt_pos.2 (Real.exp_pos _)
    exact vacuumRemainder_relativeBudget input x₀ hLayout (testInclusion D)
      q w (forcedDivisor C level) kernelEnvelope hw hκ hEnvelope hQuiet

end YM.Integration.LocalComparison.Global
end
