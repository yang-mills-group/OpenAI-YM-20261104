import Mathlib.RingTheory.PowerSeries.Exp

/-!
Finite-order algebra used at the conditional saddle RG08. Never evaluate a perturbation
series at nonzero coupling. `Through` is inclusive; `dict` returns to the finite
slice actually available. Vacuum calculus will use coefficients in a polynomial algebra
on finitely many site/potential parameters.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Series
open Function PowerSeries
open scoped BigOperators
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Agree through order n inclusive. -/
def Through (n : ℕ) (f g : PowerSeries R) := ∀ k ≤ n, coeff k f = coeff k g
namespace Through
variable {n m : ℕ} {f g h f' g' h' : PowerSeries R}
@[refl] lemma exact_eq (f : PowerSeries R) (n : ℕ) : Through n f f := fun _ _ => rfl
@[trans] lemma trans (hf : Through n f g) (hg : Through n g h) : Through n f h := fun i hi => (hf i hi).trans (hg i hi)
@[symm] lemma symm (hf : Through n f g) : Through n g f := fun i hi => (hf i hi).symm
lemma weaken (hp : Through n f g) (h : m ≤ n) : Through m f g := fun _ h' => hp _ (h'.trans h)
lemma apex (hp : Through n f g) : coeff n f=coeff n g := hp n (le_refl _)
lemma from_trunc (f : PowerSeries R) (n : ℕ) : Through n f (trunc (n+1) f : PowerSeries R) := fun i hi => by rw [coeff_coe_trunc_of_lt (Nat.lt_succ_of_le hi)]
lemma top (h : ∀ n : ℕ, Through n f g) : f = g := PowerSeries.ext (fun i => (h i).apex)
lemma map_left (e : R →+* S) (h : Through n f g) : Through n (f.map e) (g.map e) := fun i hi => by rw [coeff_map,coeff_map,h i hi]
lemma mul (hf : Through n f f') (hg : Through n g g') : Through n (f*g) (f'*g') := fun i hi => by
  simp_rw [coeff_mul]
  apply Finset.sum_congr rfl; intro p hp; have hj:= Finset.mem_antidiagonal.mp hp
  rw [hf p.1 (by omega), hg p.2 (by omega)]
lemma add (hf : Through n f f') (hg : Through n g g') : Through n (f+g) (f'+g') := fun i hi => by rw [map_add,map_add,hf i hi,hg i hi]
lemma sub (hf : Through n f f') (hg : Through n g g') : Through n (f-g) (f'-g') := fun i hi => by rw [map_sub,map_sub,hf i hi,hg i hi]
lemma pow (hf : Through n f f') (j : ℕ) : Through n (f^j) (f'^j) := by
  induction j with
  | zero=> simpa using! exact_eq (1 : PowerSeries R) n
  | succ j ih=> rw [pow_succ,pow_succ]; exact ih.mul hf
lemma finsetSum {α : Type*} {s : Finset α} {f g : α → PowerSeries R} (h : ∀ i ∈ s, Through n (f i) (g i)) : Through n (∑ i ∈ s, f i) (∑ i ∈ s,g i) := fun j hj => by
  rw [map_sum,map_sum];exact Finset.sum_congr rfl (fun i hi=> h i hi j hj)
end Through

lemma dict (f : PowerSeries R) (n : ℕ) : Through n f (∑ i ∈ Finset.range (n+1), C (coeff i f) * X^i) := fun j hj => by
   rw [map_sum]; simp only [coeff_C_mul, coeff_X_pow]
   rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr (by omega))]
   · simp
   intro b _ hb; simp [hb.symm]

lemma subst_coeff {f : PowerSeries R} (hf : coeff 0 f = 0) (p : PowerSeries R) (n i : ℕ) (hi : i ≤ n):
    coeff i (p.subst f) = ∑ j∈Finset.range (n+1), coeff j p * coeff i (f^j) := by
  have hc : PowerSeries.constantCoeff f=0 := (coeff_zero_eq_constantCoeff_apply f).symm.trans hf
  have hg := HasSubst.of_constantCoeff_zero' hc
  rw [coeff_subst' hg, finsum_eq_sum_of_support_subset _ (s:=Finset.range (n+1)) ?_]
  · simp only [smul_eq_mul]
  intro j hj; simp only [mem_support] at hj; by_contra! hb
  simp only [Finset.mem_coe,Finset.mem_range,not_lt] at hb
  apply hj
  have hk : (↑i : ℕ∞) < j := by exact_mod_cast show i < j by omega
  rw [PowerSeries.coeff_of_lt_order _ (hk.trans_le (le_order_pow_of_constantCoeff_eq_zero j hc)), smul_zero]

lemma Through.compose {n : ℕ} {f f' p p' : PowerSeries R}
    (hg : Through n p p') (h : Through n f f') (hf : coeff 0 f=0) : Through n (p.subst f) (p'.subst f') := by
  intro i hi; rw [subst_coeff hf p n _ hi, subst_coeff ((h 0 (by omega)).symm.trans hf) p' n _ hi]
  exact Finset.sum_congr rfl (fun j hj => by rw [hg _ (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), (h.pow j) _ hi])

lemma tribe {f : PowerSeries R} (hf : coeff 0 f = 0) : HasSubst f := HasSubst.of_constantCoeff_zero' ((coeff_zero_eq_constantCoeff_apply f).symm.trans hf)
lemma peep {f : PowerSeries R} (hf : coeff 0 f = 0) (p : PowerSeries R) : coeff 0 (p.subst f) = coeff 0 p := by simp [subst_coeff hf p 0 0 (le_refl _)]

section lift
variable {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A S]

/-- Arbitrary coefficientwise linear operations. Useful for parameter derivatives
and Gaussian integration. -/
def beam (φ : R →ₗ[A] S) : PowerSeries R →ₗ[A] PowerSeries S where
  toFun p := PowerSeries.mk (fun i => φ (coeff i p))
  map_add' f g := by ext1 i; simp
  map_smul' c f := by ext1 i; simp -- scalar action not leading PowerSeries coeff itself
@[simp] lemma coeff_beam (φ : R →ₗ[A] S) (p : PowerSeries R) (i) : coeff i (beam φ p)= φ (coeff i p) := by simp [beam]
@[simp] lemma beam_C (φ : R →ₗ[A] S) (r : R) : beam φ (C r) = C (φ r) := by ext1 i; simp [coeff_C]; split_ifs <;> simp_all
lemma beam_through (φ : R →ₗ[A] S) {f g : PowerSeries R} {n : ℕ} (h : Through n f g) : Through n (beam φ f) (beam φ g) := fun i hi => by rw [coeff_beam,coeff_beam,h i hi]

/-- Coefficientwise derivation (no loss of perturbative orders). -/
def shaft (d : Derivation A R R) : Derivation A (PowerSeries R) (PowerSeries R) :=
  { beam d.toLinearMap with
    map_one_eq_zero' := by ext1 i; simp [coeff_one]; split_ifs <;> simp_all
    leibniz' p q := by
      ext1 i;change coeff i (beam _ _) = coeff i (_ * _ + _ * _)
      simp_rw [map_add,coeff_beam,coeff_mul,coeff_beam,map_sum,show ⇑d.toLinearMap = ⇑d from rfl,Derivation.leibniz,smul_eq_mul,Finset.sum_add_distrib]
      -- symmetry
      congr 1
      exact Finset.Nat.sum_antidiagonal_swap (n:=i) (f:=fun j => coeff j.1 q * d (coeff j.2 p)) }
@[simp] lemma coeff_shaft (d : Derivation A R R) (p : PowerSeries R) (i) : coeff i (shaft d p) = d (coeff i p) := coeff_beam d.toLinearMap p i
@[simp] lemma shaft_C (d : Derivation A R R) (x : R) : shaft d (C x) = C (d x) := beam_C d.toLinearMap x
end lift
end YM.FormalBulk08.Series
