import YM.Integration.LocalFormalCoefficients
import YM.Integration.RunFormalChain

/-! Local formal coefficients on the retained physical Run.

The formal chain is supplied by this Run's existing prices, kinetic data
and exact history identities. It is fixed once before orders or marker
queries. No independent construction or existence choice occurs here.
These remain local conditional coefficients, not terminal correlations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.LocalFormal
open Marker Comparison.RG02 PhysicalNext.Repeat.Legato

variable {G : Gauge} (R : Run G)
    {V : Type} [DecidableEq V] [Fintype V] {A : Census V}
    (D : Datum R.family A)

/-- Ordinary local formal coefficients using the one chain of this Run. -/
def runCoefficients (r k : ℕ) (mode : A.Mode) : ℂ :=
  D.ordinaryCoefficient (RunFormalChain.fromRun R) r k mode

/-- The actual retained Run supplies every construction-side premise for
the formal numerator/denominator identities. -/
theorem run_normalization (r : ℕ) :
    let Y := RunFormalChain.fromRun R
    D.denominator Y r * D.ordinary Y r = D.raw Y r ∧
      Order.denominator (D.ordinary Y r) = 1 ∧
      Order.denominator (D.markedLog Y r) = 0 := by
  exact ⟨D.reconstruct (RunFormalChain.fromRun R) r,
    D.ordinary_denominator (RunFormalChain.fromRun R) r,
    D.markedLog_denominator (RunFormalChain.fromRun R) r⟩

/-- Changing a local tag leaves the same Run's full formal coefficient
unchanged; neither the chain nor the physical Family is reselected. -/
theorem run_coefficient_retag
    (tag : (R.family.path.levels.clock.op D.level D.period).Choices)
    (r k : ℕ) (mode : A.Mode) :
    runCoefficients R (D.retag tag) r k mode = runCoefficients R D r k mode :=
  D.ordinaryCoefficient_retag (RunFormalChain.fromRun R) tag r k mode

end YM.Integration.LocalFormal
