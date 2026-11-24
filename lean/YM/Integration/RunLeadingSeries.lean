import YM.Integration.ActualLeadingSeries
import YM.Integration.RunLeadingIR

/-! The full calibrated source-series leading limit on the retained Run.
The original construction supplies the valuation; no discrepancy estimate
or replacement family is supplied as an additional premise. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.RunLeadingSeries

open Filter Lattice Wilson Source PowerSeries
open XSpace XSpace.Outline ActualLeadingIR PhysicalNext.Repeat.Legato
open scoped BigOperators Classical Topology

variable {G : Gauge} (R : Run G) {I : Type*} [Fintype I] (d : I → ℕ)

theorem comparison :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (N p : ℕ) (v : (i : I) → R.family.label (d i))
      (T : (actualPeriod R.family N p).Tree) (o : Cover),
      Comets.Tall (actualPeriod R.family N p) o → ∀ (r : ℕ) (x : I → Cover),
      (∀ i, Sail.reach (x i - o) ≤ r) →
      engineeringScale R.family d N *
        ‖coeff 0 (ActualLeadingSeries.series R.family N p d T x v) -
          cover R.family d (engineeredInput R.family d N v) x‖ ≤
        A * Comets.budget (actualPeriod R.family N p) r * inputMass R.family d v :=
  ActualLeadingSeries.comparison R.family d
    (fun i => CoefficientBridge.run_valuation R (d i))

theorem error_tendsto (N r : ℕ)
    (v : (p : ℕ) → (i : I) → R.family.label (d i)) (M : ℝ)
    (hmass : ∀ᶠ p in atTop, inputMass R.family d (v p) ≤ M)
    (T : (p : ℕ) → (actualPeriod R.family N p).Tree)
    (o : ℕ → Cover) (x : ℕ → I → Cover)
    (hbulk : ∀ᶠ p in atTop, Comets.Tall (actualPeriod R.family N p) (o p) ∧
      ∀ i, Sail.reach (x p i - o p) ≤ r) :
    Tendsto (fun p => coeff 0
      (ActualLeadingSeries.series R.family N p d (T p) (x p) (v p)) -
      cover R.family d (engineeredInput R.family d N (v p)) (x p)) atTop (𝓝 0) :=
  ActualLeadingSeries.error_tendsto R.family d
    (fun i => CoefficientBridge.run_valuation R (d i)) N r v M hmass T o x hbulk

end YM.Integration.RunLeadingSeries
