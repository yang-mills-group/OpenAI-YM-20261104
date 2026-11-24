import MSOrdinaryOPE
import MSReference
import YangMills.WilsonProof.NativeSupport.YangMills.FreeFields

/-! The ordinary perturbative OPE is determined by inserting its output field
in the same continuum correlation functions with arbitrary exterior fields.
The coefficients at unit relative length are read from polynomials in minus
the logarithm of the length. All positions here are relative to the fusion
center. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.MSbar.Ordinary

open Filter Set
open scoped Topology BigOperators Classical

variable {g : GaugeGroup} (B : Maxwell.Reference g)

/-- At exact output weight w and perturbative order k the price is a physical
polynomial operator, with log-coordinate t and dimensionless inner shape x. -/
abbrev Price (n : ℕ) := (w k : ℕ) → ℝ → Points n → B.sector w










end YangMills.MSbar.Ordinary
