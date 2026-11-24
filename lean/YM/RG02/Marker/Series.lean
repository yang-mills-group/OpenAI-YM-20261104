import YM.RG02.Marker.Grade
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Formal coupling jets with marker coefficients

`basepoint` is the entry without coupling powers *and* without markers.
Formal logarithms/exponentials in the joint ideal are finite through every
fixed coupling order. `den` retains **all** coupling entries of the vacuum,
used in division for the marked answer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Grade
open Marker Extra.Trajectories Marks PowerSeries Finset
open scoped BigOperators
variable {ι : Type} [DecidableEq ι] {R : Census ι}

abbrev Script (R : Census ι) := PowerSeries (Poly R)

/-- Evaluate the table on empty source demand. -/
def blank (R : Census ι) : Poly R →+* ℂ where
  toFun x := x.part R.quiet
  map_mul' x y := Poly.quiet_mul x y
  map_one' := by simp
  map_zero' := Poly.part_nil _
  map_add' _ _ := Poly.part_plus ..
def den : Script R →+* PowerSeries ℂ := PowerSeries.map (blank R)
def scalar (R : Census ι) : PowerSeries ℂ →+* Script R := PowerSeries.map (Poly.bead R)

def basepoint : Script R →+* ℂ := PowerSeries.constantCoeff.comp den

@[simp] theorem den_scalar (x : PowerSeries ℂ) : den (scalar R x)=x := by
  ext n; rw [scalar,den,coeff_map,coeff_map]; simp [blank,Poly.bead]

theorem basepoint_read (x : Script R) : basepoint x=(coeff 0 x).part R.quiet := by
  rw [basepoint,RingHom.comp_apply, ← coeff_zero_eq_constantCoeff_apply,den, coeff_map]; rfl

theorem hasDen (x : Script R) : constantCoeff (den x)=basepoint x := rfl

section Ratio
def quotient (x : Script R) : Script R := scalar R (den x)⁻¹ * x


lemma den_quotient {x : Script R} (hx : basepoint x ≠ 0) : den (quotient x) = 1 := by
  rw [quotient,map_mul,den_scalar]
  exact PowerSeries.inv_mul_cancel _ (by rwa [hasDen])

theorem unnormalized {x : Script R} (hx : basepoint x ≠ 0) : scalar R (den x)*quotient x = x := by
  rw [quotient, ← mul_assoc, ← map_mul,PowerSeries.mul_inv_cancel _ (by rwa [hasDen]),map_one,one_mul]
end Ratio

lemma series_ext {x y : Script R} (h : ∀ k : ℕ, encode k x=encode k y) : x=y :=
  PowerSeries.ext fun k => encode_same.mp (h k) k le_rfl

theorem encode_quiet (r : ℕ) (x : Script R) : (encode r x).part (mixed r R).quiet=basepoint x := by
  rw [encode_part,Pair.fst_quiet,Pair.snd_quiet]
  simp only [Census.quiet,Finset.card_empty,Nat.factorial_zero,Nat.cast_one,one_mul]
  exact (basepoint_read x).symm

theorem encode_smul (r : ℕ) (x : Script R) (c : ℂ) : encode r (c • x)= c • encode r x := by
  ext i; rw [Poly.part_smul, encode_part, encode_part,PowerSeries.coeff_smul,Poly.part_smul]; ring

theorem encode_sub (r : ℕ) (x y : Script R) : encode r (x-y)=encode r x-encode r y := map_sub (encodeHom ..) ..

theorem encode_sum {J : Type*} (r : ℕ) (s : Finset J) (x : J → Script R) :
    encode r (∑ i∈s,x i)=∑ i∈s,encode r (x i) := map_sum (encodeHom ..) ..

section Fin
variable [Fintype ι]

lemma excess {x : Script R} (hx : basepoint x = 0) (n k : ℕ) (h : n + Fintype.card ι < k) :
    coeff n (x^k) = 0 := by
  have he : encode n (x^k) = encode n (0 : Script R) := by
    rw [encode_pow,encode_zero]; exact Poly.stops _ ((encode_quiet ..).trans hx) k (by simpa using h)
  exact (encode_same.mp he n le_rfl).trans (map_zero _)

def exponential (x : Script R) : Script R := PowerSeries.mk fun k =>
  coeff k (∑ j∈range (k + Fintype.card ι + 1), (j.factorial:ℂ)⁻¹ • x^j)

lemma exponential_terms {x : Script R} (hx : basepoint x = 0) (k j : ℕ) (he : k+Fintype.card ι < j) :
    coeff k (exponential x) = coeff k (∑ i∈Finset.range j,(i.factorial:ℂ)⁻¹ • x^i) := by
  rw [exponential,PowerSeries.coeff_mk,map_sum,map_sum]
  apply Finset.sum_subset (range_mono he)
  intro i _ hi
  simp only [mem_range,not_lt] at hi
  rw [PowerSeries.coeff_smul,excess hx k i (by omega),smul_zero]

theorem encode_exponential {x : Script R} (hx : basepoint x = 0) (r : ℕ) :
    encode r (exponential x) = Poly.pass (encode r x) := by
  rw [encode_same.mpr (show ∀ i, i≤r → coeff i (exponential x) =
    coeff i (∑ j∈range (r+Fintype.card ι+1),(j.factorial:ℂ)⁻¹ • x^j) from
      fun i hi => exponential_terms hx _ _ (by omega))]
  unfold Poly.pass; rw [encode_sum]
  simp only [encode_smul,encode_pow,Fintype.card_sum,Fintype.card_fin]

def logarithm (x : Script R) : Script R := PowerSeries.mk fun k =>
  coeff k (∑ j∈range (k+Fintype.card ι), (((-1:ℂ)^j)/(j+1:ℂ)) • (x-1)^(j+1))

lemma logarithm_terms {x : Script R} (hx : basepoint x=1) (k j : ℕ) (he : k+Fintype.card ι ≤ j) :
    coeff k (logarithm x) = coeff k
      (∑ i∈range j, (((-1:ℂ)^i)/(i+1:ℂ)) • (x-1)^(i+1)) := by
  rw [logarithm,PowerSeries.coeff_mk,map_sum,map_sum]
  apply Finset.sum_subset (range_mono he)
  intro i _ hi
  simp only [mem_range,not_lt] at hi
  have h := show basepoint (x-1)=0 from by rw [map_sub,hx,map_one,sub_self]
  rw [PowerSeries.coeff_smul,excess h k (i+1) (by omega), smul_zero]

theorem encode_logarithm {x : Script R} (hx : basepoint x = 1) (r : ℕ) :
    encode r (logarithm x)=connected (encode r x) := by
  rw [encode_same.mpr (show ∀ i, i≤r → coeff i (logarithm x) =
    coeff i (∑ j∈range (r+Fintype.card ι), (((-1:ℂ)^j)/(j+1:ℂ)) • (x-1)^(j+1)) from
    fun i hi => logarithm_terms hx _ _ (by omega)), connected_eq_logTable ((encode_quiet r x).trans hx)]
  unfold logTable; rw [encode_sum]; simp only [encode_smul,encode_pow,encode_sub,encode_one,
    Fintype.card_sum,Fintype.card_fin]

@[simp] lemma base_exponential {x : Script R} (hx : basepoint x=0) : basepoint (exponential x)=1 := by
  rw [← encode_quiet 0,encode_exponential hx]; exact Poly.pass_part _ ((encode_quiet ..).trans hx)

@[simp] lemma base_logarithm {x : Script R} (hx : basepoint x=1) : basepoint (logarithm x)=0 := by
  rw [← encode_quiet 0,encode_logarithm hx]; exact connected_quiet ((encode_quiet ..).trans hx)

theorem exp_log {x : Script R} (hx : basepoint x=1) : exponential (logarithm x)=x := by
  apply series_ext; intro k
  rw [encode_exponential (base_logarithm hx),encode_logarithm hx,
    pass_connected ((encode_quiet k x).trans hx)]

theorem log_exp {x : Script R} (hx : basepoint x=0) : logarithm (exponential x)=x := by
  apply series_ext; intro k
  rw [encode_logarithm (base_exponential hx),encode_exponential hx,
    recover_connected ((encode_quiet k x).trans hx)]

theorem exponential_add {x y : Script R} (hx : basepoint x=0) (hy : basepoint y=0) :
    exponential (x+y)=exponential x * exponential y := by
  apply series_ext; intro k
  rw [encode_exponential (by simp only [map_add,hx,hy,add_zero]), encode_add,encode_mul,
    encode_exponential hx,encode_exponential hy,pass_add ((encode_quiet k x).trans hx) ((encode_quiet k y).trans hy)]

theorem logarithm_mul {x y : Script R} (hx : basepoint x=1) (hy : basepoint y=1) :
    logarithm (x*y) = logarithm x + logarithm y := by
  apply series_ext; intro k
  rw [encode_logarithm (by simp only [map_mul,hx,hy,mul_one]),encode_mul,
    connected_mul ((encode_quiet ..).trans hx) ((encode_quiet ..).trans hy), encode_add,
    encode_logarithm hx,encode_logarithm hy]

@[simp] theorem exponential_zero : exponential (0 : Script R)=1 := by
  apply series_ext; intro k; rw [encode_exponential (map_zero _),encode_zero,encode_one,pass_zero]

@[simp] theorem logarithm_one : logarithm (1 : Script R)=0 := by
  have hx := log_exp (x:= (0:Script R)) (map_zero _)
  rwa [exponential_zero] at hx

-- Also an encoding of just the vacuum part on the SAME marker census.
private lemma retainedLog {x : Script R} (hx : den x = 1) : den (logarithm x)=0 := by
  have ht : basepoint x=1 := by rw [← hasDen,hx,map_one]
  ext k
  rw [den,coeff_map,logarithm_terms ht _ _ (le_refl _), map_sum,map_sum]
  rw [map_zero (coeff k)]
  refine sum_eq_zero fun i _ => ?_
  rw [coeff_smul]; change ((_ : ℂ) • (_ : Poly R)).part R.quiet=0
  rw [Poly.part_smul]; apply mul_eq_zero_of_right; change blank R (coeff k ((x-1)^(i+1))) = 0
  rw [← coeff_map (blank R)]
  change coeff k (den ((x-1)^(i+1)))=0
  rw [map_pow, map_sub,hx,map_one,sub_self,zero_pow (by omega),map_zero (coeff k)]

/-- The pure-vacuum contraction of marked log after conditional division
is exactly zero, at all grades (not assuming the denominator has no
coupling dependence). -/
theorem vacuum_cancel {x : Script R} (h : basepoint x ≠ 0) :
    den (logarithm (quotient x))=0 := retainedLog (den_quotient h)

/-- For a normalized action at (joint) origin, discard vacuum-only
graphs AFTER log/moment integration and division. -/
theorem vacuum_graphs {x : Script R} (h : basepoint x=1) :
    logarithm (quotient x) = logarithm x - logarithm (scalar R (den x)) := by
  have he : basepoint x ≠ 0 := by rw [h]; simp
  have hv := den_quotient he
  apply eq_sub_of_add_eq
  rw [add_comm, ← logarithm_mul, unnormalized he]
  · simp only [← hasDen, den_scalar]; exact h
  simp only [← hasDen, hv, map_one]

end Fin
end YM.RG02.Grade
