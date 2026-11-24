import YM.Integration.ActualLeadingIR
import YM.Integration.WilsonCoefficientPreparation

/-! The leading infrared comparison on the already retained Run. Its
actual source valuation is supplied by the original construction, and
all independent source coefficients remain universally quantified. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.RunLeadingIR

open Function Filter Lattice Wilson Source
open XSpace XSpace.Outline XSpace.Comets
open ActualLeadingIR PhysicalNext.Repeat.Legato
open scoped BigOperators Classical Topology

variable {G : Gauge} (R : Run G) {I : Type*} [Fintype I] (d : I → ℕ)

/-- The source valuation is discharged on this exact Run. The constant
precedes all UV cutoffs, periods, tree choices, positions and test inputs. -/
theorem comparison :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (N : ℕ) (v : (i : I) → R.family.label (d i))
      (P : XSpace.Period) (T : P.Tree) (o : Cover),
      Comets.Tall P o → ∀ (r : ℕ) (x : I → Cover),
      (∀ i, Sail.reach (x i - o) ≤ r) →
      engineeringScale R.family d N *
        ‖finite R.family d (engineeredInput R.family d N v) P T x -
          cover R.family d (engineeredInput R.family d N v) x‖ ≤
        A * Comets.budget P r * inputMass R.family d v :=
  comparison_engineered R.family d (fun i => CoefficientBridge.run_valuation R (d i))

/-- Independent coefficients may vary along the very same period
sequence. Bounded input mass is the only test normalization; no error
bound is supplied as a premise. -/
theorem error_tendsto (N r : ℕ) (v : (p : ℕ) → (i : I) → R.family.label (d i))
    (M : ℝ) (hmass : ∀ᶠ p in atTop, inputMass R.family d (v p) ≤ M)
    (T : (p : ℕ) → (actualPeriod R.family N p).Tree)
    (o : ℕ → Cover) (x : ℕ → I → Cover)
    (hbulk : ∀ᶠ p in atTop, Comets.Tall (actualPeriod R.family N p) (o p) ∧
      ∀ i, Sail.reach (x p i - o p) ≤ r) :
    Tendsto (fun p => finite R.family d (v p) (actualPeriod R.family N p) (T p) (x p) -
      cover R.family d (v p) (x p)) atTop (𝓝 0) :=
  actual_uniform_error_tendsto R.family d (fun i => CoefficientBridge.run_valuation R (d i))
    N r v M hmass T o x hbulk

end YM.Integration.RunLeadingIR
