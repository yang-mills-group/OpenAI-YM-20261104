import YM.Comparison.RG02.Algebra.Polar
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Single expansion parameter & commuting marked coefficient operations

Asymptotic, not convergent, series. At total marks `v` and coupling degree `k`, at
most `v+k` logarithmic or exponential factors matter; hence the finite formulas.
Predicates `entryZero`, `entryOne` are conditions at g-degree zero **and** empty mark.
Do not take perturbative logarithms of unrescaled partition functions this way.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Comparison.RG02
open Marker Finset PowerSeries
open scoped BigOperators

/-- Marked polynomial coefficients at each ordinary power of g. -/
abbrev Tape {V : Type*} [DecidableEq V] (R : Census V) := PowerSeries (Poly R)

namespace Tape
open Extra.Trajectories
variable {V : Type*} [DecidableEq V] {R : Census V}

/-- Augmentation at both g & markers zero. -/
def entry (R : Census V) : Tape R →+* ℂ := (quietMap R).toRingHom.comp PowerSeries.constantCoeff

/-- The vacuum series SLOT; includes all orders. -/
def scalar (R : Census V) : Tape R →ₐ[ℂ] PowerSeries ℂ := mapAlgHom (quietMap R)

theorem scalar_map : (scalar R).toRingHom = PowerSeries.map (quietMap R).toRingHom := rfl

@[simp] theorem scalar_part (x : Tape R) (k : ℕ) :
    coeff k (scalar R x) = (coeff k x).part R.quiet := by simp [scalar, mapAlgHom_apply]

def entryZero (x : Tape R) := entry R x=0
def entryOne (x : Tape R) := entry R x=1

@[simp] theorem entry_coeff (x : Tape R) : entry R x = (coeff 0 x).part R.quiet := by rw [entry,RingHom.comp_apply,PowerSeries.coeff_zero_eq_constantCoeff_apply]; rfl

/-- Series coefficient with some markers. -/
def read (T : R.Mode) (x : Tape R) : PowerSeries ℂ := mk fun i => (coeff i x).part T

@[simp] theorem read_coeff (T : R.Mode) (x : Tape R) (k : ℕ) : coeff k (read T x) =
    (coeff k x).part T := coeff_mk k _

/-- Lift scalar to all g-degrees, vacuum mode. -/
def fixScalar (R : Census V) : PowerSeries ℂ →ₐ[ℂ] Tape R :=
    mapAlgHom (Algebra.ofId ℂ (Poly R))

@[simp] theorem fixScalar_part (u : PowerSeries ℂ) (k : ℕ) (p : R.Mode) :
    (coeff k (fixScalar R u)).part p = if p=R.quiet then coeff k u else 0 := by
  simp only [fixScalar,mapAlgHom_apply,coeff_map,AlgHom.coe_toRingHom]; exact Poly.part_send ..

@[simp] theorem scalar_fix (u : PowerSeries ℂ) : scalar R (fixScalar R u)=u := by
  ext k; simp

def eject (x : Tape R) : Tape R := x - fixScalar _ (scalar _ x)
@[simp] theorem scalar_eject (x : Tape R) : scalar R (eject x)=0 := by simp [eject]

lemma empty_coeff_of_noScalar (x : Tape R) (h : scalar R x=0) (k : ℕ) :
    (coeff k x).part R.quiet = 0 := by rw [← scalar_part, h,map_zero]

lemma entry_of_noScalar (x : Tape R) (h : scalar R x=0) : entryZero x := by rw [entryZero,entry_coeff]; exact empty_coeff_of_noScalar x h 0

lemma same_order_zero (x y : Tape R) {r : ℕ} (h : sameThrough r x y) : entry R x = entry R y := by
   simp only [entry_coeff,h _ (Nat.zero_le r)]

section
variable [Fintype V]

/-- Formal truncated-at-each-coefficient exponential. Requires `entryZero`. -/
def exponential (x : Tape R) : Tape R :=
   PowerSeries.mk fun i => coeff i (expTerms (i + Fintype.card V) x)

/-- Formal truncated-at-each-coefficient natural logarithm. Requires `entryOne`. -/
def logarithm (x : Tape R) : Tape R :=
   PowerSeries.mk fun i => coeff i (logTerms (i + Fintype.card V) x)

theorem powered_zero {x : Tape R} (hx : entryZero x) (n m : ℕ) (h : n + Fintype.card V < m) :
    sameThrough n (x^m) 0 := by
   apply Polar.encode_iff.mp
   rw [map_pow, Poly.stops, map_zero]
   · rw [Polar.encode_quiet, ← entry_coeff]; exact hx
   simpa using h

theorem exponential_cut_of {x : Tape R} (hx : entryZero x) {n m : ℕ} (h : n+Fintype.card V ≤ m) :
    sameThrough n (exponential x) (expTerms m x) := by
   intro i hi
   rw [exponential, coeff_mk]
   unfold expTerms
   rw [map_sum,map_sum]
   refine sum_subset (range_mono (by omega)) fun j _ hj => ?_
   have he := (powered_zero hx i j (by simp only [mem_range, not_lt] at hj; omega)) i le_rfl
   rw [PowerSeries.coeff_smul, he, map_zero, smul_zero]

theorem logarithm_cut_of {x : Tape R} (hx : entryOne x) {n m : ℕ} (h : n+Fintype.card V ≤ m) :
    sameThrough n (logarithm x) (logTerms m x) := by
   intro i hi
   rw [logarithm, coeff_mk]
   unfold logTerms
   rw [map_sum,map_sum]
   refine sum_subset (range_mono (by omega)) fun j _ hj => ?_
   have hv : entryZero (x-1) := by rw [entryZero, map_sub, hx,map_one,sub_self]
   have he := (powered_zero hv i (j+1) (by simp only [mem_range, not_lt] at hj; omega)) i le_rfl
   rw [PowerSeries.coeff_smul, he, map_zero, smul_zero]

theorem polar_exp {x : Tape R} (n : ℕ) (hx : entryZero x) :
     Polar.encode n R (exponential x) = (Polar.encode n R x).pass := by
   rw [Polar.encode_iff.mpr (exponential_cut_of hx le_rfl)]
   unfold expTerms Poly.pass
   simp

theorem polar_log {x : Tape R} (n : ℕ) (hx : entryOne x) :
     Polar.encode n R (logarithm x) = connected (Polar.encode n R x) := by
   rw [Polar.encode_iff.mpr (logarithm_cut_of hx le_rfl), ← logTerms_eq]
   · unfold logTerms; simp
   rw [Polar.encode_quiet, ← entry_coeff]; exact hx

theorem entry_exp {x : Tape R} (hx : entryZero x) : entryOne (exponential x) := by
   rw [entryOne, entry_coeff, ← Polar.encode_quiet (r:=0), polar_exp _ hx,
     Poly.pass_part _ ?_]
   rw [Polar.encode_quiet, ← entry_coeff]; exact hx

theorem entry_log {x : Tape R} (hx : entryOne x) : entryZero (logarithm x) := by
   rw [entryZero, entry_coeff, ← Polar.encode_quiet (r:=0), polar_log _ hx]
   apply connected_quiet; rw [Polar.encode_quiet, ← entry_coeff]; exact hx

private theorem polar_ext {x y : Tape R} (h : ∀ i, Polar.encode i R x = Polar.encode i R y) : x=y := by
   exact PowerSeries.ext fun i => Polar.encode_iff.mp (h i) i le_rfl

theorem exponential_logarithm {x : Tape R} (hx : entryOne x) : exponential (logarithm x) = x := by
   refine polar_ext fun i => ?_
   rw [polar_exp _ (entry_log hx), polar_log _ hx, pass_connected]
   rw [Polar.encode_quiet, ← entry_coeff]; exact hx

theorem logarithm_exponential {x : Tape R} (hx : entryZero x) : logarithm (exponential x) = x := by
   refine polar_ext fun i => ?_
   rw [polar_log _ (entry_exp hx), polar_exp _ hx, Comparison.RG02.connected_pass]
   rw [Polar.encode_quiet, ← entry_coeff]; exact hx

theorem exponential_sum {x y : Tape R} (hx : entryZero x) (hy : entryZero y) :
    exponential (x+y)=exponential x * exponential y := by
   refine polar_ext fun i => ?_
   rw [map_mul, polar_exp _ hx, polar_exp _ hy, polar_exp, map_add, pass_add]
   · rw [Polar.encode_quiet, ← entry_coeff]; exact hx
   · rw [Polar.encode_quiet, ← entry_coeff]; exact hy
   rw [entryZero,map_add,hx,hy,zero_add]

theorem logarithm_product {x y : Tape R} (hx : entryOne x) (hy : entryOne y) :
    logarithm (x*y)=logarithm x + logarithm y := by
   refine polar_ext fun i => ?_
   rw [map_add, polar_log _ hx, polar_log _ hy, polar_log, map_mul, Comparison.RG02.connected_product]
   · rw [Polar.encode_quiet, ← entry_coeff]; exact hx
   · rw [Polar.encode_quiet, ← entry_coeff]; exact hy
   rw [entryOne,map_mul,hx,hy,one_mul]

@[simp] theorem exponential_zero : exponential (0:Tape R) = 1 := by
   refine polar_ext fun i => ?_
   rw [polar_exp, map_zero,map_one,pass_zero]
   exact map_zero _

@[simp] theorem logarithm_one : logarithm (1:Tape R)=0 := by
   rw [← exponential_zero (R:=R), logarithm_exponential]
   exact map_zero _

theorem exponential_cut {x y : Tape R} (hx : entryZero x) {r : ℕ} (h : sameThrough r x y) :
    sameThrough r (exponential x) (exponential y) := by
   apply Polar.encode_iff.mp
   rw [polar_exp _ hx, polar_exp, Polar.encode_iff.mpr h]
   exact ((same_order_zero x y h).symm).trans hx

theorem logarithm_cut {x y : Tape R} (hx : entryOne x) {r : ℕ} (h : sameThrough r x y) :
    sameThrough r (logarithm x) (logarithm y) := by
   apply Polar.encode_iff.mp
   rw [polar_log _ hx, polar_log, Polar.encode_iff.mpr h]
   exact ((same_order_zero x y h).symm).trans hx
end

-- Naturality for a map of marker algebras preserving the quiet part.
section Map
variable {V' : Type*} [DecidableEq V'] {R' : Census V'}

lemma carry (F : Poly R →ₐ[ℂ] Poly R') (H : ∀ x, quietMap R' (F x) = quietMap R x)
    (x : Tape R) : scalar R' (PowerSeries.mapAlgHom F x) = scalar R x := by
  ext i
  simp [mapAlgHom_apply, ← quietMap_apply, ← H]

lemma entry_maps (F : Poly R →ₐ[ℂ] Poly R') (H : ∀ x, quietMap R' (F x) = quietMap R x)
    (x : Tape R) : entry R' (PowerSeries.mapAlgHom F x) = entry R x := by
  simp only [entry_coeff, ← scalar_part, carry F H]

variable [Fintype V] [Fintype V']

lemma exponential_maps (F : Poly R →ₐ[ℂ] Poly R') (H : ∀ x, quietMap R' (F x) = quietMap R x)
    {x : Tape R} (h : entryZero x) : mapAlgHom F (exponential x) = exponential (mapAlgHom F x) := by
  have ht := (entry_maps F H x).trans h
  apply PowerSeries.ext
  intro i
  let n := (i+Fintype.card V)+(Fintype.card V')
  have he : coeff i (exponential x)=coeff i (expTerms n x) := exponential_cut_of h (n:=i) (by omega) i le_rfl
  rw [mapAlgHom_apply, coeff_map, he, exponential_cut_of (show entryZero _ from ht) (m:=n)
    (n:=i) (by omega) i le_rfl, ← coeff_map, ← mapAlgHom_apply]
  simp only [expTerms,map_sum,map_pow,map_smul]

lemma logarithm_maps (F : Poly R →ₐ[ℂ] Poly R') (H : ∀ x, quietMap R' (F x) = quietMap R x)
    {x : Tape R} (h : entryOne x) : mapAlgHom F (logarithm x) = logarithm (mapAlgHom F x) := by
  let y := logarithm x
  have hy := entry_log h
  have hh := exponential_logarithm h
  nth_rw 2 [← hh]
  rw [exponential_maps F H hy, logarithm_exponential]
  exact (entry_maps F H y).trans hy

lemma scalar_exponential (x : Tape R) (h : entryZero x) :
    exponential (fixScalar R (scalar R x)) = fixScalar _ (scalar R (exponential x)) := by
  let f : Poly R →ₐ[ℂ] Poly R := (Algebra.ofId ℂ (Poly R)).comp (quietMap R)
  have hf p : quietMap R (f p)=quietMap R p := (quietMap R).commutes _
  have hF (p) : mapAlgHom f p=fixScalar R (scalar R p) := by
    apply PowerSeries.ext; intro k; rw [mapAlgHom_apply,coeff_map,fixScalar,scalar,mapAlgHom_apply,mapAlgHom_apply,coeff_map,coeff_map]; rfl
  simp_rw [← hF]; exact (exponential_maps f hf h).symm

lemma scalar_logarithm (x : Tape R) (h : entryOne x) :
    logarithm (fixScalar R (scalar R x)) = fixScalar _ (scalar R (logarithm x)) := by
  let w:=logarithm x
  have hw := entry_log h
  have hv : entryZero (fixScalar R (scalar R w)) := by
    unfold entryZero; rw [entry_coeff, ← scalar_part, scalar_fix, scalar_part, ← entry_coeff]; exact hw
  have he:= exponential_logarithm h
  have ht:=scalar_exponential w hw
  rw [show w.exponential=x from he] at ht
  rw [← ht,logarithm_exponential hv]

end Map

-- Explicit denominator. Remark: PowerSeries.⁻¹ requires a division ring so
-- first extract the scalar in ℂ⟦X⟧. Don't discard its g-dependence.
def normal (x : Tape R) := x * fixScalar _ (scalar R x)⁻¹

lemma unit_term (x : Tape R) (h : entryOne x) : constantCoeff (scalar R x) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, scalar_part, ← entry_coeff]; exact h

lemma normal_scalar {x : Tape R} (h : entryOne x) : scalar R (normal x)=1 := by
  rw [normal,map_mul, scalar_fix, PowerSeries.mul_inv_cancel]
  rw [unit_term x h]; exact one_ne_zero

lemma entry_normal {x : Tape R} (h : entryOne x) : entryOne (normal x) := by
  rw [entryOne,entry_coeff, ← scalar_part, normal_scalar h]; exact PowerSeries.coeff_zero_one

lemma normal_mul {x : Tape R} (h : entryOne x) : fixScalar R (scalar R x) * normal x = x := by
  unfold normal
  rw [mul_left_comm, ← map_mul, PowerSeries.mul_inv_cancel, map_one, mul_one]
  rw [unit_term x h]; exact one_ne_zero

section
variable [Fintype V]

-- conditional cumulant after common normalization, includes field-independent marks.
def hotLog (x : Tape R) : Tape R := logarithm (normal x)

lemma scalar_hotLog {x : Tape R} (h : entryOne x) : scalar R (hotLog x)=0 := by
  have he := scalar_logarithm (normal x) (entry_normal h)
  rw [normal_scalar h, map_one, logarithm_one] at he
  unfold hotLog
  rw [← scalar_fix (R:=R) (scalar R (logarithm x.normal)), ← he,map_zero]

lemma logarithm_split {x : Tape R} (h : entryOne x) :
    logarithm x = fixScalar R (scalar R (logarithm x)) + hotLog x := by
  have hv : entryOne (fixScalar R (scalar R x)) := by rw [entryOne,entry_coeff, ← scalar_part, scalar_fix,scalar_part, ← entry_coeff]; exact h
  calc
    _ = logarithm (fixScalar R (scalar R x)) + hotLog x := by rw [hotLog, ← logarithm_product hv (entry_normal h), normal_mul h] -- may unfold hotlog
    _ = _ := by rw [scalar_logarithm _ h]

lemma erase_vacuum {x : Tape R} (h : entryOne x) : hotLog x = eject (logarithm x) := by
  unfold eject
  nth_rw 1 [logarithm_split h]
  rw [add_sub_cancel_left]

/-- Exact cancellation after subtracting BOTH the marked model and the vacuum series in
an exponent. No division of actual densities asserted by this identity. -/
theorem subtract_exponent {x : Tape R} (h : entryOne x) :
    x * exponential (-(fixScalar R (scalar R (logarithm x)) + hotLog x)) = 1 := by
   rw [← logarithm_split h]
   calc
    _ = exponential (logarithm x) * exponential (- logarithm x) := by rw [exponential_logarithm h]
    _ = 1 := by
      rw [← exponential_sum (entry_log h) (show entryZero (-x.logarithm) by
        rw [entryZero,map_neg,entry_log h,neg_zero]), add_neg_cancel, exponential_zero]

end

end Tape
end YM.Comparison.RG02
