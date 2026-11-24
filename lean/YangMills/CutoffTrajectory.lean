import YangMills.LatticeFields

/-! The cutoff sequence and bare couplings of a Wilson family. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.Wilson

open Filter
open scoped Topology

variable {g : GaugeGroup}

/-- Ratio of consecutive inverse lattice spacings. -/
def wilsonBlock (C : WilsonFamily g) (m : ℕ) : ℕ :=
  (C.denominator (m + 1)).val / (C.denominator m).val

/-- Relative logarithmic advance of the cutoff at grade `m`. -/
def wilsonLogStep (C : WilsonFamily g) (m : ℕ) : ℝ :=
  Real.log (wilsonBlock C m : ℝ) / Real.log ((C.denominator m).val : ℝ)

/-- The one-loop center of the finite bare interval, in Wilson action units. -/
def wilsonBareCenter (B : Maxwell.Reference g) (C : WilsonFamily g)
    (reference : ℝ) (N : ℕ) : ℝ :=
  reference + (2 * wilsonOneLoop B) * Real.log ((C.denominator N).val : ℝ)

/-- One calendar and one reference inverse coupling for all admitted cutoffs
and periods. The intervals constrain the actual parameter of `wilsonLaw`. -/
structure WilsonTrajectory (B : Maxwell.Reference g) (C : WilsonFamily g) : Prop where
  denominatorZero : (C.denominator 0).val = 1
  divides (m : ℕ) : (C.denominator m).val ∣ (C.denominator (m + 1)).val
  blockOdd (m : ℕ) : Odd (wilsonBlock C m)
  blockLarge (m : ℕ) : 3 ≤ wilsonBlock C m
  periodFour (p : ℕ) : 4 ∣ (C.period p).val
  gentle : Tendsto (wilsonLogStep C) atTop (𝓝 0)
  bare : ∃ reference : ℝ, 0 < reference ∧ (∀ p, C.beta 0 p = reference) ∧
    ∀ N p, C.beta N p ∈ Set.Icc (wilsonBareCenter B C reference N / 2)
      (2 * wilsonBareCenter B C reference N)

end YangMills.Wilson
