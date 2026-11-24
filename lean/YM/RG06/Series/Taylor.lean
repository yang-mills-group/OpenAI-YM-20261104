import YM.RG06.Series.TaylorLegacy
import YM.Pert.Lattice.Series
import Mathlib.Analysis.Calculus.Taylor
/-!
# Ordinary Taylor series interface for stencil insertions

Purely coefficientwise. Real line derivatives; the common log-link scale is
real. No assumptions that smooth functions equal sums of their series.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06
namespace GSeries
open scoped BigOperators Classical ContDiff

variable {A E F : Type*}
section Analytic
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Avoid factorial arithmetic until needed. Taylor values with order k and
any real center. -/
def offer (t : ℝ) (k : ℕ) (f : ℝ → E) := (k.factorial : ℝ)⁻¹ • iteratedDeriv k f t

@[simp] theorem offer_zero (t : ℝ) (f : ℝ → E) : offer t 0 f = f t := by
  simp [offer]

theorem offer_add (t : ℝ) (k : ℕ) {f g : ℝ → E}
    (hf : ContDiffAt ℝ k f t) (hg : ContDiffAt ℝ k g t) :
    offer t k (f+g) = offer t k f + offer t k g := by
  unfold offer; rw [iteratedDeriv_add hf hg, smul_add]

theorem offer_clm (t : ℝ) (k : ℕ) {f : ℝ → E} (L : E →L[ℝ] F)
    (hf : ContDiffAt ℝ k f t) : offer t k (L ∘ f) = L (offer t k f) := by
  simp only [offer,iteratedDeriv_eq_iteratedFDeriv]
  rw [L.iteratedFDeriv_comp_left hf le_rfl, L.map_smul]; rfl

theorem offer_sum (t : ℝ) (k : ℕ) {I : Type*} (s : Finset I) (f : I → ℝ → E)
    (hf : ∀ i ∈ s, ContDiffAt ℝ k (f i) t) :
    offer t k (fun z=> ∑ i ∈ s, f i z) = ∑ i∈s, offer t k (f i) := by
  unfold offer; rw [iteratedDeriv_fun_sum hf,Finset.smul_sum]
end Analytic

section Series
variable [NormedRing A] [NormedAlgebra ℝ A]

-- Allow A = G.Mat (noncommutative) to avoid a decomposition into entries in the path
-- compiler. `PowerSeries A` has Semiring/Ring not algebraMap/LinearMap for A→PowerSeries A?

private theorem offer_grade (t : ℝ) (n i : ℕ) (hi : i≤n) (f g : ℝ → A) :
    (n.factorial : ℝ)⁻¹ •
      ((n.choose i : A) * iteratedDeriv i f t * iteratedDeriv (n-i) g t) =
      offer t i f * offer t (n-i) g := by
  let a := iteratedDeriv i f t
  let b := iteratedDeriv (n-i) g t
  change (n.factorial : ℝ)⁻¹ • ((n.choose i : A) * a * b) =
    ((i.factorial : ℝ)⁻¹ • a) * ((Nat.factorial (n-i) : ℝ)⁻¹ • b)
  rw [mul_assoc,← nsmul_eq_mul,
    ← Nat.cast_smul_eq_nsmul ℝ (n.choose i) (a*b), Algebra.smul_mul_assoc,
    Algebra.mul_smul_comm,smul_smul,smul_smul]
  congr 1
  have he : (n.choose i : ℝ) * i.factorial * (n-i).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  field_simp
  exact he

theorem offer_mul (t : ℝ) (n : ℕ) {f g : ℝ → A}
    (hf : ContDiffAt ℝ n f t) (hg : ContDiffAt ℝ n g t) :
    offer t n (f*g) = ∑ ij∈Finset.antidiagonal n, offer t ij.1 f * offer t ij.2 g := by
  unfold offer -- use sum_antidiagonal_mk matcher
  rw [iteratedDeriv_mul hf hg, Finset.smul_sum,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _]
  exact Finset.sum_congr rfl fun i hi => offer_grade t n i (by simpa using hi) ..

/-- All Taylor coefficients assembled in an ordinary power series. -/
def assembler (t : ℝ) (f : ℝ → A) : PowerSeries A := PowerSeries.mk fun k => offer t k f

@[simp] lemma assembler_coeff (t : ℝ) (f : ℝ → A) (k : ℕ) :
    PowerSeries.coeff k (assembler t f) = offer t k f := PowerSeries.coeff_mk ..

lemma at_order (k : ℕ) : (↑k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr (le_top (a := (↑k : ℕ∞)))

lemma assembler_const (t : ℝ) (a : A) :
    assembler t (fun _ => a) = PowerSeries.C a := by
  ext1 k; cases k <;> simp [PowerSeries.coeff_C,offer,iteratedDeriv_const]

lemma assembler_add (t : ℝ) {f g : ℝ → A} (hf : ContDiffAt ℝ ∞ f t) (hg : ContDiffAt ℝ ∞ g t) :
    assembler t (f+g) = assembler t f + assembler t g := by
  ext1 k; rw [assembler_coeff,offer_add _ _ (hf.of_le (at_order _)) (hg.of_le (at_order _)),map_add]; simp only [assembler_coeff]

lemma assembler_mul (t : ℝ) {f g : ℝ → A} (hf : ContDiffAt ℝ ∞ f t) (hg : ContDiffAt ℝ ∞ g t) :
    assembler t (f*g) = assembler t f * assembler t g := by
  ext1 k; rw [assembler_coeff,offer_mul _ _ (hf.of_le (at_order _)) (hg.of_le (at_order _)), PowerSeries.coeff_mul]; simp only [assembler_coeff]
end Series

/-! A relation bundling regularity and the coefficient equality. We instantiate mostly
at zero but use arbitrary centers for derivative tests. Keep ∞ smooth for convenience;
all germs we interpret here are local analytic at flat or smoother. No complex g
regularity required. -/
section Rel
variable [NormedRing A] [NormedAlgebra ℝ A]
structure Garnish (t : ℝ) (f : ℝ → A) (P : PowerSeries A) : Prop where
  smooth : ContDiffAt ℝ ∞ f t
  series : P = assembler t f
namespace Garnish
variable {t : ℝ} {f g : ℝ → A} {P Q : PowerSeries A}

theorem coeff (h : Garnish t f P) (k : ℕ) : PowerSeries.coeff k P = offer t k f := h.series ▸ assembler_coeff _ _ _

theorem constant (t : ℝ) (a : A) : Garnish t (fun _ => a) (PowerSeries.C a) :=
  ⟨contDiffAt_const, (assembler_const t a).symm⟩

theorem zero (t : ℝ) : Garnish t (0 : ℝ → A) 0 := by
  change Garnish t (fun _=> (0:A)) 0; simpa only [map_zero] using constant t (0:A)
theorem one (t : ℝ) : Garnish t (1 : ℝ → A) 1 := by
  change Garnish t (fun _=> (1:A)) 1; simpa only [map_one] using constant t (1:A)

theorem add (h : Garnish t f P) (i : Garnish t g Q) : Garnish t (f+g) (P+Q) :=
  ⟨h.smooth.add i.smooth, by rw [h.series,i.series,assembler_add t h.smooth i.smooth]⟩
theorem mul (h : Garnish t f P) (i : Garnish t g Q) : Garnish t (f*g) (P*Q) :=
  ⟨h.smooth.mul i.smooth, by rw [h.series,i.series,assembler_mul t h.smooth i.smooth]⟩

theorem C_mul (a : A) (h : Garnish t f P) : Garnish t (fun r => a * f r) (PowerSeries.C a * P) := (constant t a).mul h
theorem mul_C (a : A) (h : Garnish t f P) : Garnish t (fun r => f r * a) (P * PowerSeries.C a) := h.mul (constant t a)
theorem neg (h : Garnish t f P) : Garnish t (-f) (-P) := by
  change Garnish t (fun r=> -f r) _; simpa using h.C_mul (-1)
theorem sub (h : Garnish t f P) (i : Garnish t g Q) : Garnish t (f-g) (P-Q) := sub_eq_add_neg f g ▸ sub_eq_add_neg P Q ▸ h.add i.neg -- orientation rewriting?

theorem sum {I : Type*} {s : Finset I} (f : I → ℝ → A) (P : I → PowerSeries A)
    (h : ∀ i∈s,Garnish t (f i) (P i)) : Garnish t (∑ i∈s,f i) (∑ i∈s,P i) := by
  induction s using Finset.induction_on with
  | empty => simpa using zero (A:=A) t
  | insert a s hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (h a (Finset.mem_insert_self ..)).add (ih fun i hi=>h i (Finset.mem_insert_of_mem hi))

theorem fun_sum {I : Type*} {s : Finset I} (f : I → ℝ → A) (P : I → PowerSeries A)
    (h : ∀ i∈s,Garnish t (f i) (P i)) : Garnish t (fun r=>∑ i∈s,f i r) (∑ i∈s,P i) := by
  simp_rw [← Finset.sum_apply]; exact Garnish.sum f P h

end Garnish

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

def reCoeff (L : A →ₗ[ℝ] B) (P : PowerSeries A) : PowerSeries B :=
  PowerSeries.mk fun k => L (PowerSeries.coeff k P)
@[simp] theorem coeff_reCoeff (L : A →ₗ[ℝ] B) (P : PowerSeries A) (k : ℕ) :
    PowerSeries.coeff k (reCoeff L P) = L (PowerSeries.coeff k P) := PowerSeries.coeff_mk ..

namespace Garnish
variable {t : ℝ} {f : ℝ → A} {P : PowerSeries A} (h : Garnish t f P)
include h
theorem linear (L : A →L[ℝ] B) : Garnish t (fun r=> L (f r)) (reCoeff L.toLinearMap P) := by
  refine ⟨L.contDiff.contDiffAt.comp t h.smooth,?_⟩; ext1 k
  rw [coeff_reCoeff,h.coeff,assembler_coeff]; exact (offer_clm t k L (h.smooth.of_le (at_order _))).symm
end Garnish
end Rel

-- MvPolynomial substitution into commutative scalar functions (with their usual
-- topology, NOT a topological polynomial ring).
section Sub
variable {I : Type*}
lemma lift_poly (t : ℝ) (P : MvPolynomial I ℂ)
    (f : I → ℝ → ℂ) (g : I → PowerSeries ℂ) (h : ∀ i, Garnish t (f i) (g i)) :
    Garnish t (fun r => MvPolynomial.eval (fun i => f i r) P) (MvPolynomial.eval₂Hom PowerSeries.C g P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval₂Hom_C,MvPolynomial.eval_C]; exact Garnish.constant t a
  | add q p ha hb => simp only [map_add]; exact ha.add hb
  | mul_X q i ha => simp only [map_mul,MvPolynomial.eval₂Hom_X',MvPolynomial.eval_X]; exact ha.mul (h i)

lemma lift_mark (t : ℝ) (P : MvPolynomial I ℂ)
    (f : I → ℝ → ℂ) (g : I → PowerSeries ℂ) (h : ∀ i, Garnish t (f i) (g i)) :
    Garnish t (fun r => MvPolynomial.aeval (fun i => f i r) P) (MvPolynomial.eval₂Hom PowerSeries.C g P) :=
  lift_poly t P f g h -- aeval_eq_eval₂Hom/eval id? defeq
end Sub
end GSeries
end YM.RG06
