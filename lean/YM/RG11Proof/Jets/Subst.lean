import YM.RG11Proof.Jets.Congr
/-! Formal coupling composition at finite precision. Inverse via mathlib
`substInvOfIsUnit`, uniqueness with finite (not all future) orders.
`Anchored` here is only the zero constant coefficient, not a parity hypothesis.
On ℝ series these are compatible with the algebra of
`YM.PertExtension.Position.Triangle` (use mathlib's fixed `PowerSeries.subst`;
keep that triangle's scalar-product mark and centering hypotheses for any
use at separated tests). No radius or actual inverse estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Jets
open PowerSeries YM.PertExtension.Position
open scoped BigOperators Classical

variable {R : Type*} [CommRing R]

/-- Zero constant in the expansion parameter. -/
def Anchored (p : PowerSeries R) : Prop := constantCoeff p = 0
/-- Coefficient of degree one, NO factorial. -/
def tangent (p : PowerSeries R) : R := coeff 1 p
/-- Algebraic branch condition, not the small-positive-coupling branch. -/
structure Coupling (p : PowerSeries R) : Prop where
  base : Anchored p
  nonsingular : IsUnit (tangent p)

namespace Anchored
theorem permits {p : R⟦X⟧} (hp : Anchored p) : PowerSeries.HasSubst p :=
  PowerSeries.HasSubst.of_constantCoeff_zero hp
@[simp] theorem empty : Anchored (0 : R⟦X⟧) := by simp [Anchored]
@[simp] theorem variableX : Anchored (X : R⟦X⟧) := PowerSeries.constantCoeff_X
theorem keep {p : R⟦X⟧} (h : Anchored p) (n) : Anchored (Jets.keep n p) := (keep_through n p).head.trans h
end Anchored

/-- Finite formula at *each* coefficient, zero-constant hypothesis only.
Single commutative coefficient ring (including complex). -/
theorem coeff_compose (i : ℕ) (outer inner : R⟦X⟧) (h : Anchored inner) :
    coeff i (PowerSeries.subst inner outer) = ∑ k∈Finset.range (i+1),
      coeff k outer * coeff i (inner^k) := by
  -- variant for arbitrary R of Pext `AlignSeries.subst_finite`
  rw [PowerSeries.coeff_subst' h.permits outer i,
    finsum_eq_sum_of_support_subset _ (s:=Finset.range (i+1)) ?_]
  · simp only [smul_eq_mul]
  intro k hk
  simp only [Function.mem_support] at hk
  simp only [Finset.mem_coe,Finset.mem_range]
  by_contra! hn
  apply hk
  rw [show coeff i (inner^k)=0 from PowerSeries.coeff_of_lt_order _
      (lt_of_lt_of_le (b:=(k:ℕ∞)) (by exact_mod_cast (by omega : i<k))
       (PowerSeries.le_order_pow_of_constantCoeff_eq_zero k h)), smul_zero]

theorem base_compose (outer inner : R⟦X⟧) (h : Anchored inner) :
    constantCoeff (PowerSeries.subst inner outer) = constantCoeff outer := by
  simp only [← coeff_zero_eq_constantCoeff_apply, coeff_compose _ _ _ h]; simp

theorem Anchored.compose {outer inner : R⟦X⟧} (ho : Anchored outer) (hi : Anchored inner) :
    Anchored (PowerSeries.subst inner outer) := (base_compose _ _ hi).trans ho

theorem tangent_compose (outer inner : R⟦X⟧) (hi : Anchored inner) :
    tangent (PowerSeries.subst inner outer) = tangent outer * tangent inner := by
  simp [tangent, coeff_compose _ _ _ hi, Finset.sum_range_succ]

theorem Coupling.compose {outer inner : R⟦X⟧} (ho : Coupling outer) (hi : Coupling inner) :
    Coupling (PowerSeries.subst inner outer) := ⟨ho.base.compose hi.base, by
      rw [tangent_compose _ _ hi.base]; exact ho.nonsingular.mul hi.nonsingular⟩

namespace Through

theorem compose {outer outer' inner inner' : R⟦X⟧} {n : ℕ} (ho : Through n outer outer')
    (hi : Through n inner inner') (hb : Anchored inner) :
    Through n (PowerSeries.subst inner outer) (PowerSeries.subst inner' outer') := by
  have he : Anchored inner' := hi.head.symm.trans hb
  intro i hin
  rw [coeff_compose _ _ _ hb, coeff_compose _ _ _ he]; refine Finset.sum_congr rfl ?_
  intro k hk
  simp only [Finset.mem_range] at hk
  rw [ho k (by omega), hi.pow k i hin]
end Through

/-- The finite-compatible formal change determined by an admissible ruler. -/
def reverse (p : R⟦X⟧) (h : Coupling p) : PowerSeries R :=
  substInvOfIsUnit p h.nonsingular

theorem reverse_good (p : R⟦X⟧) (h : Coupling p) : Coupling (reverse p h) :=
  ⟨PowerSeries.constantCoeff_substInvOfIsUnit .., by simp [reverse,tangent]⟩

theorem reverse_compose_apply (p : R⟦X⟧) (h : Coupling p) : PowerSeries.subst p (reverse p h) = X :=
  PowerSeries.subst_substInvOfIsUnit_left p h.base h.nonsingular

theorem compose_reverse_apply (p : R⟦X⟧) (h : Coupling p) : PowerSeries.subst (reverse p h) p = X :=
  PowerSeries.subst_substInvOfIsUnit_right p h.base h.nonsingular

@[simp] theorem reverse_reverse_compose (p q : R⟦X⟧) (h : Coupling p) :
    PowerSeries.subst p (PowerSeries.subst (reverse p h) q) = q := by
  rw [subst_comp_subst_apply (T:=R) (reverse_good p h).base.permits h.base.permits,
    reverse_compose_apply, X_subst]

@[simp] theorem compose_reverse_compose (p q : R⟦X⟧) (h : Coupling p) :
    PowerSeries.subst (reverse p h) (PowerSeries.subst p q) = q := by
  rw [subst_comp_subst_apply (T:=R) h.base.permits (reverse_good p h).base.permits,
    compose_reverse_apply, X_subst]

theorem reverse_unique_through {p q : R⟦X⟧} (h : Coupling p) {n : ℕ}
    (he : Through n (PowerSeries.subst p q) X) : Through n q (reverse p h) := by
  have H := he.compose (Through.refl (reverse p h)) (reverse_good p h).base
  rwa [compose_reverse_compose,subst_X ((reverse_good p h).base.permits)] at H

-- Use just the same *n*-jet, not order n+1.
theorem Through.reverse {p q : R⟦X⟧} {n : ℕ} (he : Through n p q) (h : Coupling p) (hg : Coupling q) :
    Through n (Jets.reverse p h) (Jets.reverse q hg) := by
  apply reverse_unique_through hg
  have H := (Through.refl (n:=n) (Jets.reverse p h)).compose he h.base
  rw [reverse_compose_apply] at H
  exact H.symm

-- No interaction in a detector array is identified by these lemmas. They
-- extend `Strike` to describe the cost of the same-parameter substitution
-- at the current order and will be used to PROVE a finite detector equation.
section hit
variable {p q : R⟦X⟧} {n : ℕ} {c : R}

theorem strike_below (h : Strike n p q c) {m : ℕ} (hm : m<n) : Through m p q :=
  fun i hi => h.lower i (hi.trans_lt hm)
theorem strike_full (h : Through n p q) : Strike n p q 0 :=
  ⟨fun i hi => h i hi.le, by rw [add_zero,h n (le_refl _)]⟩
theorem strike_minus_of_prior (h : ∀ i<n, coeff i p = coeff i q) :
    Strike n p q (coeff n q - coeff n p) :=
  ⟨h, by simp⟩
theorem strike_trans {p' : R⟦X⟧} {d : R} (hp : Strike n p q c) (hq : Strike n q p' d) :
    Strike n p p' (c+d) := ⟨fun i hi => (hp.lower i hi).trans (hq.lower i hi), by
      rw [← add_assoc, hp.value, hq.value]⟩

theorem strike_pow (hn : 0<n) (hz : Anchored p) (h : Strike n p q c) (k : ℕ) :
    Strike n (p^k) (q^k) (if k=1 then c else 0) := by
  induction k with
  | zero => simpa only [pow_zero,Nat.zero_ne_add_one,↓reduceIte] using
      Strike.same (n:=n) (1:R⟦X⟧)
  | succ k H =>
    rw [pow_succ,pow_succ]
    have hw := H.mul hn h
    have he : (constantCoeff (R:=R)) p = 0 := hz
    by_cases h₀:k=0
    · subst k; simpa only [pow_zero,map_one,zero_add,zero_mul,mul_zero,he,if_true,one_mul] using hw
    simpa [map_pow, he,h₀] using hw

theorem strike_recouple (outer : R⟦X⟧) (hn : 0<n) (hz : Anchored p) (h : Strike n p q c) :
    Strike n (PowerSeries.subst p outer) (PowerSeries.subst q outer) (tangent outer*c) := by
  have he : Anchored q := (strike_below h hn).head.symm.trans hz
  constructor
  · intro i hi
    exact ((Through.refl outer).compose (strike_below h hi) hz) i (le_refl _)
  rw [coeff_compose _ _ _ hz, coeff_compose _ _ _ he]
  have hj : ∑ k∈Finset.range (n+1), coeff k outer*(if k=1 then c else 0) = tangent outer*c := by
    rw [Finset.sum_eq_single_of_mem 1 (by simp [hn]) (fun j _ h' => by simp [h'])]; simp [tangent]
  rw [← hj, ← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun k _=> ?_)
  rw [← mul_add, (strike_pow hn hz h k).value]
end hit
end YM.RG11.Jets
