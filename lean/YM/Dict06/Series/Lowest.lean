import YM.Dict06.Series.Germ
import Mathlib.Algebra.MvPolynomial.Basic

/-! Ordinary (not exponential generating) coefficient calculus for the
lowest allowed rank of a stencil. Valid also for a zero leading value;
never requires domain/no zero divisors. Noncommutative for the link side;
commutative when multiplying scalar columns. -/
set_option autoImplicit false
noncomputable section
namespace YM.Dict06.Series
open PowerSeries
open scoped BigOperators
section Basic
variable {R : Type*} [Semiring R]
structure Initial (n : ℕ) (s : PowerSeries R) (x : R) : Prop where
  zero i : i<n→ coeff i s=0
  lead : coeff n s=x

namespace Initial
variable {n m : ℕ} {s t : PowerSeries R} {x y : R}

lemma relax (h : Initial n s x) (hle : m<n) : Initial m s 0 := ⟨fun i hi=>h.zero i (hi.trans hle),h.zero _ hle⟩
lemma lower (h : Initial n s x) (hle : m≤n) :
    Initial m s (if m=n then x else 0) := by
  rcases eq_or_lt_of_le hle with rfl|hl
  · simpa using h
  simpa only [if_neg hl.ne] using h.relax hl
lemma add (h : Initial n s x) (g : Initial n t y) : Initial n (s+t) (x+y) := by
  refine ⟨fun i hi => ?_,?_⟩
  · rw [_root_.map_add, h.zero i hi,g.zero i hi,zero_add]
  rw [_root_.map_add,h.lead,g.lead]
lemma sum {I : Type*} (a : Finset I) (f : I→PowerSeries R) (v : I→R)
    (hf : ∀i∈a, Initial n (f i) (v i)) : Initial n (∑ i∈a,f i) (∑ i∈a,v i) := by
  refine ⟨fun j hj=>?_,?_⟩
  · rw [_root_.map_sum]; exact Finset.sum_eq_zero (fun i hi=>(hf i hi).zero _ hj)
  rw [_root_.map_sum]; exact Finset.sum_congr rfl fun i hi=>(hf i hi).lead
lemma mul (h : Initial n s x) (g : Initial m t y) : Initial (n+m) (s*t) (x*y) := by
  classical
  constructor
  · intro k hk; rw [coeff_mul]
    apply Finset.sum_eq_zero; rintro ⟨i,j⟩ he
    have he' : i+j=k := Finset.mem_antidiagonal.mp he
    change coeff i _ * coeff j _=0
    rcases lt_or_ge i n with hi|hi
    · rw [h.zero i hi,zero_mul]
    rw [g.zero j (by omega),mul_zero]
  rw [coeff_mul,Finset.sum_eq_single (n,m)]
  · change coeff n _ * coeff m _=_; rw [h.lead,g.lead]
  · rintro ⟨i,j⟩ he hv
    have he' : i+j=n+m := Finset.mem_antidiagonal.mp he
    change coeff i _ * coeff j _=0
    rcases lt_or_ge i n with hi|hi
    · rw [h.zero i hi,zero_mul]
    rw [g.zero j ?_,mul_zero]
    have he : i ≠ n ∨ j ≠ m := by by_contra! hg; exact hv (Prod.ext hg.1 hg.2)
    omega
  · intro he; exact False.elim (he (Finset.mem_antidiagonal.mpr rfl))
lemma constant (x : R) : Initial 0 (C x) x := ⟨by simp,coeff_zero_C x⟩
lemma scalar (h : Initial n s x) (c : R) : Initial n (C c * s) (c*x) := by simpa using (constant c).mul h
lemma unit : Initial 0 (1:PowerSeries R) 1:=⟨by simp,coeff_zero_one⟩
lemma pow (h : Initial n s x) (k : ℕ) : Initial (n*k) (s^k) (x^k) := by
  induction k with
  | zero => simpa using! (unit (R:=R))
  | succ k ih => simpa only [pow_succ, Nat.mul_succ] using ih.mul h
end Initial
end Basic

section Comm
variable {I R : Type*} [CommSemiring R]
lemma Initial.prod (f:I→ PowerSeries R) (x:I→R) (d:I→ℕ) (s:Finset I)
    (hf : ∀i∈s, Initial (d i) (f i) (x i)) :
    Initial (∑i∈s,d i) (∏i∈s,f i) (∏i∈s,x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using! (Initial.unit (R:=R))
  | insert i s hi ih=>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).mul (ih fun j hj=>hf j (Finset.mem_insert_of_mem hj))

open MvPolynomial (support)

def count (i : I →₀ ℕ) : ℕ := i.sum fun _ k => k
lemma Initial.scalarPoly (p : MvPolynomial I R) (n:ℕ) (f:I→ PowerSeries R) (x:I→R)
    (hf: ∀ i, Initial 1 (f i) (x i)) (hp : ∀ i∈p.support, n ≤ count i) :
    Initial n (MvPolynomial.eval₂Hom PowerSeries.C f p)
      (∑ i∈p.support,
        if count i=n then (MvPolynomial.coeff i p) * ∏ j∈i.support, (x j) ^ (i j)
        else 0) := by
  classical
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  apply Initial.sum _ _ _; intro i hi
  have he : Initial (count i) (∏ j ∈ i.support, (f j)^i j) (∏ j∈i.support, (x j)^i j):= by
    apply Initial.prod (d:=fun j=>i j) -- reducible count?
    intro j _; simpa using (hf j).pow (i j)
  by_cases ha : count i=n
  · rw [if_pos ha]; rw [ha] at he; exact he.scalar _
  rw [if_neg ha]
  exact ((he.scalar (MvPolynomial.coeff i p)).relax (lt_of_le_of_ne (hp _ hi) (Ne.symm ha)))
end Comm
end YM.Dict06.Series
