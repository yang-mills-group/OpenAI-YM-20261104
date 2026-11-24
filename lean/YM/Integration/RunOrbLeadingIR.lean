import YM.Integration.ActualOrbLeadingIR
import YM.Integration.RunLeadingSeries

/-! The original normalized inversion quotient on the retained Run.
Finite-regulator series identification is all-order; the proved IR
removal here concerns its leading slot-divided coefficient at fixed UV. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.RunOrbLeadingIR

open Filter Lattice Wilson Source PowerSeries
open XSpace XSpace.Outline ActualLeadingIR PhysicalNext.Repeat.Legato
open scoped BigOperators Classical Topology

variable {G : Gauge} (R : Run G) {I : Type*} [Fintype I] (d : I → ℕ)

theorem series_eq_orbitSeries (N p : ℕ) (T : (actualPeriod R.family N p).Tree)
    (x : I → Cover) (v : (i : I) → R.family.label (d i)) :
    ActualLeadingSeries.series R.family N p d T x v =
      ActualOrbLeadingIR.orbitSeries R.family N p d x v :=
  ActualOrbLeadingIR.series_eq_orbitSeries R.family N p d x R.makes
    (fun i => CoefficientBridge.run_valuation R (d i)) T v

theorem comparison :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (N p : ℕ) (v : (i : I) → R.family.label (d i))
      (_T : (actualPeriod R.family N p).Tree) (o : Cover),
      Comets.Tall (actualPeriod R.family N p) o → ∀ (r : ℕ) (x : I → Cover),
      (∀ i, Sail.reach (x i - o) ≤ r) →
      engineeringScale R.family d N *
        ‖coeff 0 (ActualOrbLeadingIR.orbitSeries R.family N p d x v) -
          cover R.family d (engineeredInput R.family d N v) x‖ ≤
        A * Comets.budget (actualPeriod R.family N p) r * inputMass R.family d v :=
  ActualOrbLeadingIR.comparison R.family d R.makes
    (fun i => CoefficientBridge.run_valuation R (d i))

theorem error_tendsto (N r : ℕ)
    (v : (p : ℕ) → (i : I) → R.family.label (d i)) (M : ℝ)
    (hmass : ∀ᶠ p in atTop, inputMass R.family d (v p) ≤ M)
    (T : (p : ℕ) → (actualPeriod R.family N p).Tree)
    (o : ℕ → Cover) (x : ℕ → I → Cover)
    (hbulk : ∀ᶠ p in atTop, Comets.Tall (actualPeriod R.family N p) (o p) ∧
      ∀ i, Sail.reach (x p i - o p) ≤ r) :
    Tendsto (fun p => coeff 0
      (ActualOrbLeadingIR.orbitSeries R.family N p d (x p) (v p)) -
      cover R.family d (engineeredInput R.family d N (v p)) (x p)) atTop (𝓝 0) :=
  ActualOrbLeadingIR.error_tendsto R.family d R.makes
    (fun i => CoefficientBridge.run_valuation R (d i)) N r v M hmass T o x hbulk

end YM.Integration.RunOrbLeadingIR
