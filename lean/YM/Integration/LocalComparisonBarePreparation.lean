import YM.Integration.LocalComparisonGlobalContract
import YM.Integration.LocalComparisonVacuumRemainder

/-! Structural preparation of an already-proved full bare input.
The actual input Taste and every independent test are retained. The auxiliary
remainder keeps the same full vacuum gas and original nonempty layout; only
its own marked coefficients vanish. This is not an inherited-remainder
propagation theorem and does not prove the supplied analytic factorization. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.LocalComparison.Global
open Lattice Wilson RG Marker
open RG3.Script.Picnic

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
  {R : Census V} {C : Family G} {D : V → ComparisonDensity.Address.Orbit}

/-- A complete all-test bare factorization gives the literal Prepared input
without altering its original represented polynomial or dropping vacuum K.
The positivity of the actual forced divisor follows from its definition. -/
def Prepared.of_bare_factorization
    (N period level : ℕ) (Q : StepCarrier C N period level)
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
    Prepared N period level Q roots input colors packets w kernelEnvelope 0 where
  convention := hColors
  remainder := vacuumRemainder input
  regular_zero _ _ := rfl
  unit_zero _ _ := rfl
  caption_zero _ _ := rfl
  full x U := by
    rw [vacuumRemainder_density input x U (hGas U)]
    simpa only [mul_smul_comm, mul_one] using hFactor x U
  forced_price := by
    have hκ : 0 < forcedDivisor C level := by
      change 0 < Real.sqrt (Real.exp _)
      exact Real.sqrt_pos.2 (Real.exp_pos _)
    exact vacuumRemainder_relativeBudget input x₀ hLayout (testInclusion D)
      (C.path.levels.budget level) w (forcedDivisor C level) kernelEnvelope
      hw hκ hEnvelope hQuiet

end YM.Integration.LocalComparison.Global
