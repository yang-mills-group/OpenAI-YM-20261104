import YM.Source.Construction

/-!
# L1 coefficient bills including omitted powers

Finite series *only*. In particular allow every symmetry factor/substitution
already in the coefficient. Useful for final precision after normalization,
as well as checking that reexpression of kinetic/coefficient data through a
fixed truncation retains order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Series
open Function Set Polynomial
open scoped BigOperators

section
variable {R : Type*} [SeminormedRing R]
def mass (p : Polynomial R) := ∑ i∈p.support, ‖p.coeff i‖

/-- Vanishes through order n-1. -/
def cut (p : Polynomial R) (n : ℕ) : Prop := ∀ j<n,p.coeff j=0
def short (p : Polynomial R) (n : ℕ) : Prop := ∀ j≥n,p.coeff j=0

variable (p q : Polynomial R)
lemma mass_nn : 0 ≤ mass p := Finset.sum_nonneg fun _ _=> norm_nonneg _
lemma mass_coeff (i : ℕ) : ‖p.coeff i‖ ≤ mass p := by
  by_cases h : i∈p.support
  · exact Finset.single_le_sum (fun _ _=>norm_nonneg _ ) h
  rw [show p.coeff i=0 from notMem_support_iff.mp h,norm_zero]; exact mass_nn p
lemma bigger (s : Finset ℕ) (hp : p.support⊆s) : mass p=∑ i∈s, ‖p.coeff i‖ := by
  classical
  exact Finset.sum_subset hp (fun i _ hi=> by rw [notMem_support_iff.mp hi,norm_zero])
lemma mass_add : mass (p+q) ≤ mass p+mass q := by
  classical
  let s := p.support ∪ q.support
  rw [bigger (p+q) s (support_add ..), bigger p s Finset.subset_union_left, bigger q s Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _=> by rw [coeff_add]; exact norm_add_le ..
@[simp] lemma mass_zero : mass (0 : Polynomial R) = 0 := by simp [mass]
lemma mass_sum {I : Type*} (s : Finset I) (f : I→Polynomial R) :
    mass (∑ i∈s,f i) ≤ ∑ i∈s, mass (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi h =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (mass_add ..).trans (add_le_add_right h _)
@[simp] lemma prices_monomial (x : R) (n : ℕ) : mass (monomial n x)=‖x‖ := by
  classical
  rw [bigger _ _ (support_monomial_subset n x)]; simp
@[simp] lemma prices_const (x : R) : mass (C x)=‖x‖ := prices_monomial x 0
lemma mass_mul : mass (p*q) ≤ mass p*mass q := by
  classical
  nth_rw 1 [p.as_sum_support, q.as_sum_support]
  rw [Finset.sum_mul]
  conv_rhs => unfold mass
  rw [Finset.sum_mul]
  refine (mass_sum ..).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact (mass_sum ..).trans (Finset.sum_le_sum fun j _=> by rw [monomial_mul_monomial, prices_monomial]; exact norm_mul_le ..)
@[simp] lemma mass_neg : mass (-p) = mass p := by simp [mass]
lemma mass_sub : mass (p-q) ≤ mass p+mass q := by rw [sub_eq_add_neg]; exact (mass_add ..).trans_eq (by rw [mass_neg])
lemma cut_support (n : ℕ) : cut p n ↔ ∀ i∈p.support,n ≤ i := by
  constructor
  · intro h i hi
    have he : p.coeff i ≠ 0 := mem_support_iff.mp hi
    exact le_of_not_gt (he ∘ h i)
  intro h i hi; exact notMem_support_iff.mp (fun hp=> hi.not_ge (h i hp))
lemma cutoff {n : ℕ} (h : cut p n) : X^(n:ℕ) ∣ p := X_pow_dvd_iff.mpr h
lemma cuts {k : ℕ} (h : X^(k:ℕ) ∣ p) : cut p k := X_pow_dvd_iff.mp h
variable [NormOneClass R]
lemma norm_read {n : ℕ} {x : R} (h : cut p n) (hx : ‖x‖≤1) : ‖p.eval x‖≤ mass p * ‖x‖^n := by
  classical
  nth_rw 1 [p.as_sum_support]; unfold mass
  rw [eval_finsetSum, Finset.sum_mul]; apply (norm_sum_le ..).trans
  refine Finset.sum_le_sum (fun i hi=> ?_)
  rw [eval_monomial]
  refine (norm_mul_le ..).trans (mul_le_mul_of_nonneg_left ((norm_pow_le ..).trans (pow_le_pow_of_le_one (norm_nonneg _) hx
    ((cut_support ..).mp h i hi))) (norm_nonneg _))
lemma cash_value {x : R} (hx : ‖x‖ ≤ 1) : ‖p.eval x‖ ≤ mass p := by simpa using! norm_read p (n:=0) (fun i hi=> by omega) hx
lemma mass_pow (n : ℕ) : mass (p^n) ≤ mass p^n := by
  induction n with
  | zero => simp only [pow_zero]; exact le_of_eq ((prices_monomial (1:R) 0).trans norm_one)
  | succ n h =>
    simp only [pow_succ]
    exact (mass_mul ..).trans (mul_le_mul_of_nonneg_right h (mass_nn p))
end
end YM.IterationFour.Series
