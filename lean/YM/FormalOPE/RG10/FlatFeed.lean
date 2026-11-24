import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.RCLike.Basic

/-!
# RG_10: from one flat conditional law and germs to coefficient integrals

Use pointwise in any *held* coarse field and at one specified step/parameters. The integration
index is **one** `(tag, field)`, including in products with multiple markers. A tag here is a
whole assignment of predictor choices, with its given probability weights; `Unit` works for a
fixed tree. `field` refers to the underlying joint Gaussian sampling variables (absorb any
coordinate choices, mean shifts etc. in the function of `(tag, field)`). The calculus works with
a base measure times a density, e.g. Gaussian probability and density one, or Lebesgue times
`exp(-quadratic)`. It permits such common flat prefactors as the integrated free determinant and
Gaussian action to be canceled. Do *not* discard a tag-dependent or source-dependent factor
on that basis. This file does not contain a tree-independence theorem.

We work coefficientwise in **g**, not β, g², threshold, or the final calibrated X-scheme
coupling. (`g` is the parameter in the prescribed rescaled germ, e.g. top `exp(g A)` links).
`Series` is a formal Taylor series (power coefficients, Taylor derivatives if used enter AFTER
dividing by factorial). No infinite-order analysis or evaluation. `Integrable` with the given
density, NOT analyticity in g, is the basic admissibility at each coefficient. Definitions using
Bochner integrals are totalized by Mathlib; interpret them as a coefficient prescription only
when the integrals exist. Some pure algebra identities don't require this.

Formal data; no interacting reports. This is an algebraic layer, intentionally parameterized by
germ/predictor/noise etc inputs (Taylor rows of actual Wilson formal kernel to be supplied in
using this for a *local Wilson cover step*). `FlatFeed` itself doesn't even stipulate gaussianity:
it suffices that in that use the supplied data be the Wilson formal flat Gaussian and vertices.
Separate theorems specialize it to Gaussian data, in particular to the WilsonX bare inversion
(tree-gauge) regulator calculation.
-/

set_option autoImplicit false
noncomputable section

namespace YM.FormalOPE.RG10
open MeasureTheory
open scoped BigOperators

abbrev Series := PowerSeries ℂ
abbrev Kernel (X : Type*) := X → Series

def row {X : Type*} (n : ℕ) (f : Kernel X) : X → ℂ := fun x => PowerSeries.coeff n (f x)

/-- Uses zero constant coefficient in its argument in this file. Finite exponential rule. -/
def expTaylor {R : Type*} [Field R] (A : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => ∑ i ∈ Finset.range (n + 1), (i.factorial : R)⁻¹ * PowerSeries.coeff n (A ^ i)

/-- Jacobians may instead be incorporated into `V` as log-Jacobians (then the producer must
supply those vertices consistently throughout). Tree gauge has no FP field. Sign convention:
`exp(+V)`, so an interaction ACTION enters `V` with MINUS sign. Vacuum scalar costs, kinetic
conventions and re-expression from adjacent coupling are NOT defined here. Remove any Laurent or
exponential prefactors common to numerator and denominator *before* making these data. -/
structure Vertices (X : Type*) where
  J : Kernel X
  V : Kernel X
  J0 : row 0 J = 1
  V0 : row 0 V = 0

namespace Vertices
variable {X : Type*} (W : Vertices X)

def weight : Kernel X := fun x => expTaylor (W.V x) * W.J x

lemma weight0 : row 0 W.weight = 1 := by
  funext x
  simp only [row, weight, PowerSeries.coeff_mul, expTaylor]
  have h : PowerSeries.coeff 0 (W.J x) = 1 := congr_fun W.J0 x
  simp [h]
end Vertices

/-- This algebraic adapter works with any given common probability choice and fields, before
cost assumptions on the covariance rows. Its instances for local steps are to use *all* formal
flat variables; in particular this is not a healthy domain restriction. Do not absorb real
exceptional-mask factors in these data. -/
structure FlatFeed (Θ E : Type*) [Fintype Θ] [MeasurableSpace E] where
  chance : Θ → ℝ
  chance_nonneg (θ : Θ) : 0 ≤ chance θ
  chance_one : ∑ θ, chance θ = 1
  base : Θ → Measure E
  density : Θ → E → ℝ
  density_nonneg (θ : Θ) : ∀ᵐ x ∂(base θ), 0 ≤ density θ x
  density_integrable (θ : Θ) : Integrable (density θ) (base θ)
  mass_pos (θ : Θ) : 0 < ∫ x, density θ x ∂(base θ)

namespace FlatFeed
variable {Θ E : Type*} [Fintype Θ] [MeasurableSpace E]
    (F : FlatFeed Θ E) (W : Vertices (Θ × E))

def mean (f : Θ × E → ℂ) : ℂ := ∑ θ, (F.chance θ : ℂ) *
  ((∫ x, (F.density θ x : ℂ) * f (θ, x) ∂(F.base θ)) /
    ((∫ x, F.density θ x ∂(F.base θ) : ℝ) : ℂ))

def Pays (f : Θ × E → ℂ) : Prop :=
  ∀ θ, Integrable (fun x => (F.density θ x : ℂ) * f (θ, x)) (F.base θ)

def average (f : Kernel (Θ × E)) : Series := PowerSeries.mk fun n => F.mean (row n f)

def Funded (f : Kernel (Θ × E)) : Prop := ∀ n, F.Pays (row n f)

lemma mean_one : F.mean 1 = 1 := by
  unfold mean
  have h (θ : Θ) : ((∫ x, F.density θ x ∂(F.base θ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (F.mass_pos θ).ne'
  simp [← Complex.ofReal_sum, integral_complex_ofReal, h, F.chance_one]

lemma average_coeff (f : Kernel (Θ × E)) (n : ℕ) :
    PowerSeries.coeff n (F.average f) = F.mean (row n f) := PowerSeries.coeff_mk ..

/-- Unmarked scalar series with the full tag and Gaussian denominator. May depend on coarse
field parameters; this is NOT necessarily one, and is not asserted equal to a course-of-history
partition function or a normalization from integrating the *coarse* kernel variable. -/
def den : Series := F.average W.weight

/-- Pre-log output, normalized conditional moment. -/
def step (f : Kernel (Θ × E)) : Series := F.average (W.weight * f) * (F.den W)⁻¹

lemma den0 : PowerSeries.coeff 0 (F.den W) = 1 := by
  rw [den, average_coeff, W.weight0, mean_one]

lemma den_inv : F.den W * (F.den W)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, F.den0]; exact one_ne_zero)

lemma step_den (f : Kernel (Θ × E)) :
    F.den W * F.step W f = F.average (W.weight * f) := by
  rw [step, mul_left_comm, den_inv, mul_one]

@[simp] lemma step_one : F.step W 1 = 1 := by rw [step, mul_one]; exact F.den_inv W

/-- Distinct slots from a set; no division by a slot factorial. In particular the pre-log output
on two distinct slots with the same field label is the moment of a PRODUCT. Used within sets of
slots allowed by the marker census; not defining any continuation of a killed (incompatible)
monomial. This is the ordinary-moment case (pure product before this step). -/
def ordinary {I : Type*} (s : Finset I) (f : I → Kernel (Θ × E)) : Series :=
  F.step W (∏ i ∈ s, f i)

lemma ordinary_pair {I : Type*} [DecidableEq I] {i j : I} (hij : i ≠ j)
    (f : I → Kernel (Θ × E)) : F.ordinary W {i,j} f = F.step W (f i * f j) := by
  simp [ordinary, hij]

/-- Connected convention for two distinct occurring slots, agree with logarithm in the
commuting square-zero marker algebra. -/
def pairConnected (f b : Kernel (Θ × E)) : Series :=
  F.step W (f * b) - F.step W f * F.step W b

end FlatFeed
end YM.FormalOPE.RG10
