import YM.XSpace.Trinity

/-! The open integer tensor of the negative-handed quadratic source against the
polarization projector of the proposed quartic-vertex graph. The Laurent integral,
color and vertex multiplicities are separate from this finite calculation. -/
namespace YM.Integration.FVA1Physical.Exchange.RoseQuartic

open Lattice XSpace.Chiral
open scoped BigOperators

def projectedGram (polar μ ν : Axis) : ℤ :=
  ∑ i : P, ∑ s : Axis, if s = polar then 0 else triCoeff false i μ s * triCoeff false i ν s

theorem projectedGram_eq : ∀ polar μ ν : Axis,
    projectedGram polar μ ν = if μ = ν then (if μ = polar then 3 else 2) else 0 := by
  decide

def strippedTwelfths (polar momentum : Axis) : ℤ :=
  (∑ μ : Axis, projectedGram polar μ μ) + 2 * projectedGram polar momentum momentum

theorem strippedTwelfths_eq : ∀ polar momentum : Axis,
    strippedTwelfths polar momentum = if polar = momentum then 15 else 13 := by
  decide

theorem transverse_fraction (polar momentum : Axis) (transverse : polar ≠ momentum) :
    (strippedTwelfths polar momentum : ℚ) / 12 = 13 / 12 := by
  norm_num [strippedTwelfths_eq, transverse]

end YM.Integration.FVA1Physical.Exchange.RoseQuartic
