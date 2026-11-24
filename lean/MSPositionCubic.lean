import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import YangMills.FreeFields

/-! Signed first-order triangle from the free Euclidean potential and the cubic
Yang–Mills vertex. All legs use orthonormal chiral two-forms. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.MSbar.Position

open MeasureTheory
open scoped BigOperators

namespace Cubic

abbrev Polarization := Fin 3
abbrev Kernel := Spacetime → ℝ
abbrev Cut := ContDiffBump (0 : Spacetime)

private def wedge (i j a b : Axis) : ℝ :=
  (if i = a ∧ j = b then 1 else 0) - (if i = b ∧ j = a then 1 else 0)

/-- Components of (e₀∧eᵢ ± eⱼ∧eₖ)/√2 for cyclic spatial indices. -/
def chiral (plus : Bool) (i : Polarization) (a b : Axis) : ℝ :=
  (Real.sqrt 2)⁻¹ * (wedge 0 i.succ a b +
    (if plus then 1 else -1) * wedge (i+1).succ (i+2).succ a b)

/-- Positive on the cyclic permutations of (0,1,2). -/
def orientation (i j k : Polarization) : ℝ :=
  (if j = i+1 ∧ k = j+1 then 1 else 0) - (if i = j+1 ∧ k = i+1 then 1 else 0)

private def potentialLine (i : Axis) (x : Spacetime) : ℝ :=
  -Maxwell.partialD i Maxwell.Coordinates.green x

private def oneCurl (p : Polarization) (b : Axis) (x : Spacetime) : ℝ :=
  ∑ a, chiral false p a b * potentialLine a x

private def contract (s t : Bool) (p r : Polarization) (a b : Axis) : ℝ :=
  ∑ i, chiral s p a i * chiral t r b i

private def twoCurls (p r : Polarization) (x : Spacetime) : ℝ :=
  ∑ a, ∑ b, contract true false p r a b * Maxwell.partialD a (potentialLine b) x

/-- Pair the derivative of the first line with the other two lines.
Outside the three cutoff balls the product is ordinary. In the ball of
the first line we integrate by parts, including the derivative of the cutoff.
In each other ball the differentiated line is smooth. -/
private def derivativeVertex (c : Cut) (a : Axis) (u v b : Spacetime)
    (f g h : Kernel) : ℝ :=
  let outside (y : Spacetime) (k : Kernel) (w : Spacetime) := (1 - c (w-y)) * k (w-y)
  let exterior (w : Spacetime) :=
    outside u (Maxwell.partialD a f) w * outside v g w * outside b h w
  let primary (w : Spacetime) :=
    let y := w + u - v
    let z := w + u - b
    f w * (-(Maxwell.partialD a (fun s => c s) w) * g y * h z -
      c w * (Maxwell.partialD a g y * h z + g y * Maxwell.partialD a h z))
  let secondary (y z : Spacetime) (k l : Kernel) (w : Spacetime) :=
    k w * c w * Maxwell.partialD a f (w+y-u) * l (w+y-z)
  (∫ w, exterior w) + (∫ w, primary w) +
    (∫ w, secondary v b g h w) + (∫ w, secondary b v h g w)

/-- The commutator part of the measured curvature and the integrated
three-gluon vertex, including the two contractions at the vertex. -/
private def vertex (c : Cut) (i j k : Polarization) (u v b : Spacetime) : ℝ :=
  let direct := ∑ a, ∑ e, chiral true i a e * oneCurl j a (u-v) * oneCurl k e (u-b)
  let bulk := ∑ r : Polarization, ∑ a : Axis, ∑ e : Axis, chiral false r a e *
    (∑ l : Axis, ∑ m : Axis, contract false true r i l m *
      derivativeVertex c l u v b (potentialLine m) (oneCurl j a) (oneCurl k e))
  direct - 2 * bulk

/-- Sum of squares of the structure constants in the public color trace form. -/
def colorNorm {g : GaugeGroup} (B : Maxwell.Reference g) : ℝ :=
  let E (i : Fin B.m) := B.matrix (EuclideanSpace.single i 1)
  let entry (a b c : Fin B.m) : ℝ :=
    -((E a * (E b * E c - E c * E b)).trace).re / ((g.n + 1 : ℕ) : ℝ)
  ∑ a : Fin B.m, ∑ b : Fin B.m, ∑ c : Fin B.m, (entry a b c)^2

end Cubic

/-- The signed real tree coefficient for the ordered cubic/quadric/quadric
triangle, on configurations with all pairwise distances larger than five times
the cutoff radius. The factor six counts the assignments to the cubic field. -/
def bareTriangle {g : GaugeGroup} (B : Maxwell.Reference g)
    (c : ContDiffBump (0 : Spacetime)) (x : Points 3) : ℝ :=
  6 * Cubic.colorNorm B * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    Cubic.orientation i j k * (∑ m : Fin 3, ∑ n : Fin 3,
      Cubic.twoCurls j m (x 0 - x 1) * Cubic.twoCurls k n (x 0 - x 2) *
        Cubic.vertex c i m n (x 0) (x 1) (x 2))

end YangMills.MSbar.Position
