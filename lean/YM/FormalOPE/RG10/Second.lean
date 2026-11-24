import YM.FormalOPE.RG10.FlatFeed
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.LinearCombination

/-! First test: the degree-2 interacting two-insertion report at one Gaussian step. Keep mean
notation to cover the shared-choice law without a false multiplicative assertion. In particular
`W.crossTwo` appears inside that expectation, with all its tags, potential legs, Jacobian and
normalized-block-rule vertices.

This file calculates the answer in terms of the finite moments of specified jets. The same
formulas cover a coarse-field output (pointwise) or a terminal step. For using these formulas as
an expansion in the general FlatFeed adapter, require `F.Funded` (at least through these
orders) on `W.weight*f` for relevant f incl products and unit; separate moment integrability
proofs if splitting those means further. As usual in such diagram tests, geometry, group,
stencils, and all flat data are parameters. This isn't asserting nonvanishing for any particular
choice. A bare Wilson specialization, with explicit plaquette vertices and identified Gaussian,
is separate.
-/

set_option autoImplicit false
noncomputable section

namespace YM.FormalOPE.RG10
open PowerSeries MeasureTheory
open scoped BigOperators

variable {X : Type*}

namespace Second
lemma mul0 {R : Type*} [CommRing R] (A B : PowerSeries R) :
    coeff 0 (A*B) = coeff 0 A * coeff 0 B := by simp [coeff_mul]
lemma mul1 {R : Type*} [CommRing R] (A B : PowerSeries R) :
    coeff 1 (A*B) = coeff 0 A * coeff 1 B + coeff 1 A * coeff 0 B := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i A * coeff j B)]
  simp [Finset.sum_range_succ]
lemma mul2 {R : Type*} [CommRing R] (A B : PowerSeries R) :
    coeff 2 (A*B) = coeff 0 A * coeff 2 B + coeff 1 A * coeff 1 B + coeff 2 A * coeff 0 B := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i A * coeff j B)]
  simp [Finset.sum_range_succ]

lemma row0 (A B : Kernel X) : row 0 (A*B) = row 0 A * row 0 B := funext fun _ => mul0 ..
lemma row1 (A B : Kernel X) : row 1 (A*B) = row 0 A * row 1 B + row 1 A * row 0 B :=
  funext fun _ => mul1 ..
lemma row2 (A B : Kernel X) : row 2 (A*B) =
    row 0 A * row 2 B + row 1 A * row 1 B + row 2 A * row 0 B := funext fun _ => mul2 ..
end Second
open Second

namespace Vertices
variable (W : Vertices X)

/-- Jacobian contributes already if nonzero in the given germ. No symmetry of the measure
is used in this test. -/
def crossOne := row 1 W.J + row 1 W.V

/-- Degree two includes the pair of grade-one action vertices AND the mixed grade-one action
and grade-one measure contributions. (For `V` the log weight rather than the action). -/
def crossTwo := row 2 W.J + row 2 W.V + (2:ℂ)⁻¹ • (row 1 W.V * row 1 W.V) + row 1 W.V * row 1 W.J

lemma weight1 : row 1 W.weight = W.crossOne := by
  funext x; unfold crossOne
  have h : coeff 0 (W.V x) = 0 := congr_fun W.V0 x
  have j : coeff 0 (W.J x) = 1 := congr_fun W.J0 x
  simp [row, weight, mul1, expTaylor, Finset.sum_range_succ, j]
lemma weight2 : row 2 W.weight = W.crossTwo := by
  funext x; unfold crossTwo
  have h : coeff 0 (W.V x) = 0 := congr_fun W.V0 x
  have j : coeff 0 (W.J x) = 1 := congr_fun W.J0 x
  simp [row, weight, mul2, expTaylor, Finset.sum_range_succ, j, h, pow_two]
  first | ac_rfl | ring
end Vertices
namespace FlatFeed
variable {Θ E : Type*} [Fintype Θ] [MeasurableSpace E] (F : FlatFeed Θ E)
    (W : Vertices (Θ × E))

/-- Explicit convolution with the interaction and Jacobian jets followed by vacuum
subtraction. Inputs already included every retained Laurent slot shift. -/
def zeroth (f0 : Θ × E → ℂ) : ℂ := F.mean f0

def first (f0 f1 : Θ × E → ℂ) : ℂ :=
  F.mean (f1 + W.crossOne * f0) - F.mean W.crossOne * F.zeroth f0

def second (f0 f1 f2 : Θ × E → ℂ) : ℂ :=
  F.mean (f2 + W.crossOne * f1 + W.crossTwo * f0) -
    F.mean W.crossTwo * F.zeroth f0 - F.mean W.crossOne * F.first W f0 f1

variable (A B : Kernel (Θ × E))

lemma step_zeroth : coeff 0 (F.step W A) = F.zeroth (row 0 A) := by
  have h := congr_arg (coeff 0) (F.step_den W A)
  rw [mul0, den0, one_mul, average_coeff, row0, W.weight0, one_mul] at h
  exact h

lemma step_first : coeff 1 (F.step W A) = F.first W (row 0 A) (row 1 A) := by
  have h := congr_arg (coeff 1) (F.step_den W A)
  rw [mul1, den0, one_mul, den, average_coeff, average_coeff, row1, W.weight1, W.weight0,
    one_mul, step_zeroth] at h
  exact eq_sub_of_add_eq h

lemma step_second : coeff 2 (F.step W A) = F.second W (row 0 A) (row 1 A) (row 2 A) := by
  have h := congr_arg (coeff 2) (F.step_den W A)
  rw [mul2, den0, one_mul, den, average_coeff, average_coeff, average_coeff, row2,
    W.weight1, W.weight2, W.weight0, one_mul, step_zeroth, step_first] at h
  exact eq_sub_of_add_eq (eq_sub_of_add_eq h)

/-- Two-insertion ordinary report at order two. Distinct allowed marks, even if the
field stencils themselves are the same. In particular `row 1 A * row 1 B` retains the
same tag AND field. -/
def mixedSecond : ℂ := F.second W
  (row 0 A * row 0 B)
  (row 0 A * row 1 B + row 1 A * row 0 B)
  (row 0 A * row 2 B + row 1 A * row 1 B + row 2 A * row 0 B)

def connectedSecond : ℂ := F.mixedSecond W A B -
  (F.zeroth (row 0 A) * F.second W (row 0 B) (row 1 B) (row 2 B) +
   F.first W (row 0 A) (row 1 A) * F.first W (row 0 B) (row 1 B) +
   F.second W (row 0 A) (row 1 A) (row 2 A) * F.zeroth (row 0 B))

theorem mixed_second : coeff 2 (F.step W (A * B)) = F.mixedSecond W A B := by
  rw [step_second, row0, row1, row2, mixedSecond]

theorem connected_second : coeff 2 (F.pairConnected W A B) = F.connectedSecond W A B := by
  rw [pairConnected, map_sub, connectedSecond, mixed_second]
  simp only [mul2, step_first, step_second, step_zeroth]

end FlatFeed
end YM.FormalOPE.RG10
