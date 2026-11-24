import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Complex.Basic

/-!
# Univariate real-analytic bookkeeping (smooth finite jet version)

Use the real log-link parameter; complexify **coefficients**, not fields. `series` is
only the sequence of Taylor coefficients; identities are coefficientwise, not assertions
about convergence. Kept generic in the output algebra so ordered matrix holonomies can
use the same convention.
-/
set_option autoImplicit false
noncomputable section
open scoped Topology ContDiff BigOperators

namespace YM.RG06
namespace Germ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- k-th real Taylor coefficient at zero; normalization by `k!` throughout. -/
def jet (f : ℝ → E) (k : ℕ) := ((k.factorial : ℝ)⁻¹) • iteratedDeriv k f 0

/-- The formal generating function of real Taylor coefficients at zero. -/
def series (f : ℝ → E) : PowerSeries E := PowerSeries.mk (jet f)

variable {f g : ℝ → E} {k : ℕ}
@[simp] theorem jet_zero : jet f 0 = f 0 := by simp [jet]
lemma jet_add (hf : ContDiffAt ℝ k f 0) (hg : ContDiffAt ℝ k g 0) :
    jet (f + g) k = jet f k + jet g k := by simp only [jet, iteratedDeriv_add hf hg, smul_add]
lemma jet_neg : jet (-f) k = - jet f k := by simp [jet]
lemma jet_const (c : E) (i : ℕ) : jet (fun _ => c) i = if i = 0 then c else 0 := by
  cases i with
  | zero => simp
  | succ i => simp [jet, iteratedDeriv_const]

theorem along (f : E → ℂ) (v : E) (hf : ContDiffAt ℝ k f 0) :
    iteratedDeriv k (fun t : ℝ => f (t • v)) 0 = iteratedFDeriv ℝ k f 0 (fun _ => v) := by
  let L := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  rcases hf.contDiffOn' le_rfl (by simp) with ⟨U,ho,hm,hU⟩
  simp only [Set.insert_eq_of_mem (Set.mem_univ _), Set.univ_inter] at hU
  have ht : IsOpen ((L : ℝ → E) ⁻¹' U) := ho.preimage L.continuous
  have he : L 0 ∈ U := by simpa using hm
  have hi := L.iteratedFDerivWithin_comp_right hU ho.uniqueDiffOn ht.uniqueDiffOn he (i:=k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen _ ht (show (0:ℝ) ∈ (L : ℝ → E) ⁻¹' U from he),
    iteratedFDerivWithin_of_isOpen _ ho he, L.map_zero] at hi
  change iteratedFDeriv ℝ k (f ∘ (L : ℝ → E)) 0 _ = _
  rw [hi]
  simp [L]

section ring
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

lemma jet_mul {f g : ℝ → A} (hf : ContDiffAt ℝ k f 0) (hg : ContDiffAt ℝ k g 0) :
    jet (f * g) k = ∑ i ∈ Finset.range (k + 1), jet f i * jet g (k-i) := by
  unfold jet
  rw [iteratedDeriv_mul hf hg, Finset.smul_sum]; apply Finset.sum_congr rfl; intro i hi
  rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul]
  congr 1
  have h0 : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  rw [Nat.cast_choose ℝ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)), div_eq_mul_inv, ← mul_assoc,
    inv_mul_cancel₀ h0, one_mul, mul_inv]

@[simp] lemma series_coeff (f : ℝ → A) (i : ℕ) : PowerSeries.coeff i (series f) = jet f i := PowerSeries.coeff_mk ..

private theorem cash (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

theorem series_add {f g : ℝ → A} (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0) :
    series (f + g) = series f + series g := by
  ext1 k
  simp [jet_add (hf.of_le (cash _)) (hg.of_le (cash _))]

theorem series_mul {f g : ℝ → A} (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0) :
    series (f * g) = series f * series g := by
  ext1 k
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simpa using jet_mul (hf.of_le (cash k)) (hg.of_le (cash k))

@[simp] theorem series_neg (f : ℝ → A) : series (-f) = -series f := by
  ext1 k; simp [jet_neg]

@[simp] theorem series_const (c : A) : series (fun _ => c) = PowerSeries.C c := by
  ext1 k
  rcases eq_or_ne k 0 with rfl|hr
  · simp
  simp [jet_const, hr, PowerSeries.coeff_C]


section comm
variable {B : Type*} [NormedCommRing B] [NormedAlgebra ℝ B]
variable {I : Type*}
open MvPolynomial

theorem pol_smooth_series (p : MvPolynomial I B) (g : I → ℝ → B)
    (hg : ∀ i, ContDiffAt ℝ ∞ (g i) 0) :
    ContDiffAt ℝ ∞ (fun t=> eval (fun i=>g i t) p) 0 ∧
    series (fun t=> eval (fun i=>g i t) p) = eval₂Hom PowerSeries.C (fun i=>series (g i)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [eval_C, contDiffAt_const,MvPolynomial.eval₂Hom_C]
  | add p q hp hq =>
      constructor
      · simpa only [map_add] using (hp.1.add hq.1)
      simp only [map_add, show (fun t=> eval (fun i=>g i t) p + eval (fun i=>g i t) q) =
        (fun t=> eval (fun i=>g i t) p) + (fun t=> eval (fun i=>g i t) q) from rfl,
        series_add hp.1 hq.1, hp.2, hq.2]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.eval₂Hom_X']
      exact ⟨hp.1.mul (hg i), show series ((fun t=> eval (fun j=>g j t) p) * g i)= _ by rw [series_mul hp.1 (hg i), hp.2]⟩
end comm
end ring
section divide
open MvPolynomial
variable {R : Type*} [CommSemiring R] {I : Type*} (v : I → R) (z : R)

/-- Scale every generator once; take the joint slot count, not engineering horizon. -/
theorem eval_monomialScale (p : MvPolynomial I R) (ℓ : ℕ)
    (hp : ∀ b ∈ p.support, b.sum (fun _ n=> n) = ℓ) :
    eval (fun i=> v i * z) p = eval v p * z^ℓ := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, eval_monomial,Finsupp.prod, mul_pow, Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [mul_assoc, ← hp b hb,Finsupp.sum]

-- eval₂ form; source coefficients needn't be scale-invariant since we scale only variables.
theorem eval₂_monomialScale {S : Type*} [CommSemiring S] (c : S →+* R) (p : MvPolynomial I S) (ℓ : ℕ)
    (hp : ∀ b ∈ p.support, b.sum (fun _ n=> n) = ℓ) :
    eval₂Hom c (fun i=> v i * z) p = eval₂Hom c v p * z^ℓ := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, eval₂Hom_monomial,Finsupp.prod, mul_pow, Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [mul_assoc, ← hp b hb,Finsupp.sum]
end divide
end Germ
end YM.RG06
