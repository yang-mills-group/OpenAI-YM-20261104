import YM.FormalOPE.RG10.Routes.Replot
import YM.FormalOPE.RG10.Routes.Debits

/-!
# Uniform through arbitrarily many steps: port rank

Constant term of tree expansion has bounded number of ports. An unmarked vertex uses at most
three additional ports per EXTRA perturbative unit (one coupling power); actually `e+2` would
suffice and is tighter for higher orders. No multiplication (or loss) on a horizontal-rank edge.
Rank condition of zero+3e boots per new step and is closed under the normalized transmission
including inverses and shifts in reexpression. Thus subsequent `Accounts` bounds, although poor
in rank, will not have hidden through-time rank explosion from assembling bundles.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route
open Function Finset PowerSeries Bulk
open MvPolynomial (totalDegree)

open Multi.Vacuum.Gauss (Row)
open scoped Topology BigOperators Classical
variable {I J B : Type}

def Guard (a : Channel I) (r d : ℕ) := ∀ i≤r,totalDegree (PowerSeries.coeff i a) ≤ d+3*i

lemma coarse_short (a : Index I B) : Primitives.GCC.LocalPolynomial.length (coarse a) ≤ Primitives.GCC.LocalPolynomial.length a := by
  have h : Primitives.GCC.LocalPolynomial.length a=rank a+Primitives.GCC.LocalPolynomial.length (coarse a) := by
    unfold rank Primitives.GCC.LocalPolynomial.length; nth_rw 1 [sound a]; rw [Finsupp.sum_sumElim]; rfl
  omega

namespace Guard
variable {d d' r k : ℕ} {a b : Channel I} (ha : Guard a r d) (hb : Guard b r d')
include ha
lemma mono (hd : d ≤ d') : Guard a r d' := fun i hi => (ha i hi).trans (Nat.add_le_add_right hd _)
lemma less (hr : k ≤ r) : Guard a k d := fun i hi => ha i (hi.trans hr)
lemma slim : Binary.slim a r (d+3*r) := fun i hi => (ha i hi).trans (by omega)
lemma trans {p : Channel I} (h : Through r a p) : Guard p r d := by intro i hi; rw [← h i hi]; exact ha i hi
include hb
lemma mul : Guard (a*b) r (d+d') := by
  intro i hi; rw [coeff_mul]; apply (MvPolynomial.totalDegree_finsetSum ..).trans; apply Finset.sup_le; intro x hx
  have he := mem_antidiagonal.mp hx; apply (MvPolynomial.totalDegree_mul ..).trans
  apply (Nat.add_le_add (ha x.1 (by omega)) (hb x.2 (by omega))).trans (by omega)
lemma plus : Guard (a+b) r (max d d') := by
  intro i hi; rw [map_add]; exact (MvPolynomial.totalDegree_add ..).trans (max_le ((mono ha (le_max_left ..)) i hi) ((mono hb (le_max_right ..)) i hi))
omit hb
lemma add (hb : Guard b r d) : Guard (a+b) r d := by simpa only [sup_idem, max_self] using plus ha hb
lemma neg : Guard (-a) r d := by intro i hi; simpa using ha i hi
lemma sub (hb : Guard b r d) : Guard (a-b) r d := by rw [sub_eq_add_neg]; exact ha.add hb.neg
lemma const_smul (c : ℂ) : Guard (c • a) r d := by intro i hi; rw [coeff_smul]; exact (MvPolynomial.totalDegree_smul_le ..).trans (ha i hi)
omit ha
lemma zero : Guard (0:Channel I) r d := by intro i _; simp
lemma one : Guard (1:Channel I) r 0 := by intro i _; rw [coeff_one]; split <;> simp
include ha
lemma pow (n : ℕ) : Guard (a^n) r (n*d) := by
  induction n with
  | zero => rw [pow_zero]; simpa only [Nat.zero_mul] using one
  | succ n ih => rw [pow_succ,Nat.add_mul,Nat.one_mul]; exact ih.mul ha
omit ha
lemma sum {Z : Type*} (A:Finset Z) (f: Z→ Channel I) (h : ∀ i∈A,Guard (f i) r d) : Guard (∑ i∈A,f i) r d := by
  induction A using Finset.induction_on with
  | empty => simp only [sum_empty]; exact zero
  | insert _ _ he ih => rw [sum_insert he]; exact add (h _ (mem_insert_self ..)) (ih (fun i hi=>h i (mem_insert_of_mem hi)))
lemma prod {Z : Type*} (A:Finset Z) (f: Z→ Channel I) (D:Z→ℕ) (h : ∀ i∈A,Guard (f i) r (D i)) : Guard (∏ i∈A,f i) r (∑ i∈A,D i) := by
  induction A using Finset.induction_on with
  | empty => simp only [prod_empty,sum_empty]; exact one
  | insert _ _ he ih => rw [sum_insert he,prod_insert he]; exact mul (h _ (mem_insert_self ..)) (ih (fun i hi=>h i (mem_insert_of_mem hi)))
lemma ignited (V : Channel I) (h : Guard V r 0) : Guard (advance V) r 0 := by
  intro i hi; rw [advance,PowerSeries.coeff_mk]; apply (MvPolynomial.totalDegree_finsetSum ..).trans; apply Finset.sup_le; intro j _
  exact (MvPolynomial.totalDegree_smul_le ..).trans (by simpa using Guard.pow h j i hi)
lemma reciprocal {p : Channel I} (h : Guard p r 0) : Guard (PowerSeries.invOfUnit p 1) r 0 := by
  intro i hi; induction i using Nat.strong_induction_on with
  | h i ih =>
    rw [coeff_invOfUnit]; split
    · simp
    rename_i h'; simp only [inv_one,Units.val_one, zero_add,neg_mul,one_mul, MvPolynomial.totalDegree_neg];
    apply (MvPolynomial.totalDegree_finsetSum ..).trans; apply Finset.sup_le; intro x hx
    split
    · rename_i hv; have he := mem_antidiagonal.mp hx;
      exact (MvPolynomial.totalDegree_mul ..).trans ((Nat.add_le_add (h x.1 (by omega)) (ih _ hv (by omega))).trans (by omega))
    simp
variable [Fintype J] (q : I → Row J) (p : Channel (I⊕B))
lemma moved (H : Guard p r d) : Guard (Bulk.move q p) r d := by
  intro i hi; rw [Bulk.move,coeff_mk,Bulk.hand]; apply (MvPolynomial.totalDegree_finsetSum ..).trans; apply Finset.sup_le; intro x hx
  exact (MvPolynomial.totalDegree_smul_le ..).trans ((MvPolynomial.totalDegree_monomial_le ..).trans ((coarse_short x).trans ((MvPolynomial.le_totalDegree hx).trans (H i hi))))
theorem transmitted (V : Channel (I⊕B)) (h : Guard V r 0) (H : Guard p r d) : Guard (Bulk.transfer q p V) r d := by
  have he := h.ignited (V:=V) -- `Guard.ignited`
  have hu := (moved q _ (he.mul H)).mul (reciprocal (moved q _ he)); simpa only [transfer,income,zero_add,Nat.add_zero] using hu
section changed
variable (T : I → Channel B) (hc : ∀ i,Guard (T i) r 1)
lemma scalar (k : ℂ) : Guard (algebraMap ℂ (Channel B) k) r 0 := by
  rw [Algebra.algebraMap_eq_smul_one]; exact one.const_smul _
include hc
lemma vars (p : Packet I) : Guard (MvPolynomial.aeval T p) r p.totalDegree := by
  nth_rw 1 [p.as_sum]; rw [map_sum]; apply Guard.sum; intro i hi
  rw [MvPolynomial.aeval_monomial]; unfold Finsupp.prod
  have h j := pow (hc j) (i j); exact mono ((scalar _).mul (prod i.support _ _ (fun j _ => h j))) (by simpa [Finsupp.sum] using MvPolynomial.le_totalDegree hi)
include ha
lemma prep : Guard (replot T a) r d := by
  intro i hi; rw [replot_coeff]; apply (MvPolynomial.totalDegree_finsetSum ..).trans; apply Finset.sup_le; intro x hx
  have he := mem_antidiagonal.mp hx; have hh := ha x.1 (by omega)
  exact (vars T hc _ x.2 (by omega)).trans (by omega)
end changed
end Guard
end YM.FormalOPE.RG10.Route
