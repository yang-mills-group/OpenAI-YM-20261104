import YM.AnalyticNext.CUBIC_MATCH.Terms.Products
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Ordinary coefficients on real field curves

Used for operator insertions. In particular we can form ordered products
(before tracing, projecting onto real color legs, etc.). Fields and
coordinates need only be given to finite order for each output coefficient.
No inversion in the Laurent/pole ring, summability prescription, or limit
in coupling is implicit in use of `PowerSeries`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Stencils
open CubicMatch
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

section Series
variable {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [NormedRing B] [NormedAlgebra ℝ B]

/-- Ordinary Taylor coefficients (divided by n!). Constant and variable are
in one real, unshifted coupling/scale here. Use with smooth germs. -/
def recording (f : ℝ → A) : PowerSeries A := PowerSeries.mk (fun n => term n f)

lemma recorded (n : ℕ) (f : ℝ → A) : PowerSeries.coeff n (recording f) = term n f := by
  unfold recording; apply PowerSeries.coeff_mk

lemma recording_congr {f g : ℝ → A} (e : Filter.EventuallyEq (nhds 0) f g) :
    recording f = recording g := PowerSeries.ext fun n =>
  (recorded n f).trans ((term_congr e).trans (recorded n g).symm)

lemma recording_linear (L : A →L[ℝ] B) {f : ℝ → A} (h : ContDiffAt ℝ ω f 0) :
    recording (fun t => L (f t)) = PowerSeries.mk (fun n => L (PowerSeries.coeff n (recording f))) := by
  apply PowerSeries.ext; intro n
  rw [recorded, PowerSeries.coeff_mk, recorded, term_linear _ (h.of_le le_top)]

lemma recording_const (c : A) : recording (fun _ => c) = PowerSeries.C c := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => rw [recorded, PowerSeries.coeff_zero_C, term_zero]
  | succ n => simp [recorded, CubicMatch.term, iteratedDeriv_const]

lemma recording_add {f g : ℝ → A} (h : ContDiffAt ℝ ω f 0) (j : ContDiffAt ℝ ω g 0) :
    recording (fun t => f t + g t) = recording f + recording g := by
  apply PowerSeries.ext; intro n
  rw [map_add, recorded, recorded, recorded, term_add (h.of_le le_top) (j.of_le le_top)]

lemma recording_sub {f g : ℝ → A} (h : ContDiffAt ℝ ω f 0) (j : ContDiffAt ℝ ω g 0) :
    recording (fun t => f t - g t) = recording f - recording g := by
  apply PowerSeries.ext; intro n
  rw [map_sub, recorded, recorded, recorded, term_sub (h.of_le le_top) (j.of_le le_top)]

lemma recording_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → A)
    (h : ∀ i ∈ s, ContDiffAt ℝ ω (f i) 0) :
    recording (fun t => ∑ i ∈ s, f i t) = ∑ i ∈ s, recording (f i) := by
  apply PowerSeries.ext; intro n
  simp only [map_sum, recorded]
  exact term_sum fun i hi => (h i hi).of_le le_top

lemma recording_mul {f g : ℝ → A} (h : ContDiffAt ℝ ω f 0) (j : ContDiffAt ℝ ω g 0) :
    recording (fun t => f t * g t) = recording f * recording g := by
  apply PowerSeries.ext; intro n
  simp only [PowerSeries.coeff_mul, recorded]
  rw [term_mul _ h j]
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => term k f * term l g) n).symm
end Series

section Commutative
variable {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]
  {σ : Type*} (p : MvPolynomial σ R) {u : σ → ℝ → R}

-- `MvPolynomial.eval`, not a complex-linear use of the path variable.
lemma smooth_pol (h : ∀ i, ContDiffAt ℝ ω (u i) 0) :
    ContDiffAt ℝ ω (fun t => MvPolynomial.eval (fun i => u i t) p) 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.eval_C]; exact contDiffAt_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, MvPolynomial.eval_X]; exact hp.mul (h i)

/-- Exact stencil-polynomial coefficient calculation. -/
theorem recording_pol (h : ∀ i, ContDiffAt ℝ ω (u i) 0) :
    recording (fun t => MvPolynomial.eval (fun i => u i t) p) =
      MvPolynomial.eval₂Hom PowerSeries.C (fun i => recording (u i)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.eval_C, MvPolynomial.eval₂Hom_C, recording_const]
  | add p q hp hq =>
    simp only [map_add]; rw [recording_add (smooth_pol p h) (smooth_pol q h), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.eval₂Hom_X']
    rw [recording_mul (smooth_pol p h) (h i), hp]
end Commutative

section SlotNormalization
variable {R : Type*} [CommSemiring R] {σ : Type*}

/-- Represented number of slots in a monomial, counted before any curvature or
polynomial identities or contractions are applied. -/
def slots (a : σ →₀ ℕ) := a.sum fun _ n => n

/-- Candidate rescaled warp of a polynomial. Use when every leg starts at
order one and `P` has no terms below slot number `ℓ`. -/
def undress (ℓ : ℕ) (P : MvPolynomial σ R) (u : σ → PowerSeries R) :=
  ∑ a ∈ P.support,
    PowerSeries.X ^ (slots a - ℓ) *
      MvPolynomial.eval₂Hom PowerSeries.C u (MvPolynomial.monomial a (P.coeff a))

lemma insert_scale_monomial (a : σ →₀ ℕ) (c : R) (t : PowerSeries R) (u : σ → PowerSeries R) :
    MvPolynomial.eval₂Hom PowerSeries.C (fun i => t * u i) (MvPolynomial.monomial a c) =
      t ^ slots a * MvPolynomial.eval₂Hom PowerSeries.C u (MvPolynomial.monomial a c) := by
  classical
  simp only [MvPolynomial.eval₂Hom_monomial]
  simp_rw [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  unfold slots Finsupp.sum
  ring

theorem undress_exact {P : MvPolynomial σ R} {ℓ : ℕ}
    (h : ∀ a ∈ P.support, ℓ ≤ slots a) (u : σ → PowerSeries R) :
    MvPolynomial.eval₂Hom PowerSeries.C (fun i => PowerSeries.X * u i) P =
      PowerSeries.X ^ ℓ * undress ℓ P u := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum, undress, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [insert_scale_monomial, ← mul_assoc, ← pow_add, Nat.add_sub_of_le (h a ha)]

lemma undress_pure {P : MvPolynomial σ R} {ℓ : ℕ}
    (h : ∀ a ∈ P.support, slots a = ℓ) (u : σ → PowerSeries R) :
    undress ℓ P u = MvPolynomial.eval₂Hom PowerSeries.C u P := by
  conv_rhs => rw [P.as_sum]
  rw [undress, map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [h a ha, Nat.sub_self, pow_zero, one_mul]
end SlotNormalization
end YM.Comparison.Stencils
