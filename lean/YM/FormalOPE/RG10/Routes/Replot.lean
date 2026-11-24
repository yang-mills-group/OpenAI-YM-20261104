import YM.FormalOPE.RG10.Restriction
import YM.FormalOPE.RG10.Routes.Channel

/-!
# Substitute a series shift in fields as well as a (same-variable) reset already on the series.

This file develops the field part. In the common-window formal reading, all kernels are in one
g, but level-i fine field `A` is the rescaled `exp(g_i(g) A)` coordinate and any coarse
`B` likewise. Consequently the flat-conditioning substitution includes also the ratio series
needed on its deterministic gradient-corrected shifts (same ratio changes on all other vertices).
This file permits that substitution including dependence on perturbative order. It is not proof of
an actual calibration or stencil change.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route
open PowerSeries Finset Function
open scoped Topology BigOperators Classical
namespace mapCoeff
variable {R S : Type*} [CommRing R] [CommRing S] (f : R→+*PowerSeries S)
local notation "P" => PowerSeries R
local notation "Q" => PowerSeries S
def push : (PowerSeries R) →+ PowerSeries S where
  toFun x := mk fun n => ∑ i∈ antidiagonal n,coeff i.2 (f (coeff i.1 x))
  map_add' x y := by apply PowerSeries.ext; intro n; simp [Finset.sum_add_distrib]
  map_zero' := by apply PowerSeries.ext; simp
lemma push_coeff (p : P) (n : ℕ) : coeff n (push f p) = ∑ i∈ antidiagonal n,coeff i.2 (f (coeff i.1 p)) := by simp [push]
lemma near_aux {p q : P} {n : ℕ} (h : Through n p q) : Through n (push f p) (push f q) := by
  intro k hk; rw [push_coeff,push_coeff]; refine sum_congr rfl fun i hi => ?_; have h' := mem_antidiagonal.mp hi
  rw [h _ (by omega)]

lemma push_mono (p : R) (v : ℕ) : push f (monomial v p)= X^v * f p := by
  apply PowerSeries.ext; intro n; rw [coeff_X_pow_mul',push_coeff];
  simp_rw [coeff_monomial]; split
  · rename_i h; rw [Finset.sum_eq_single (v,n-v)]
    · simp
    · intro i hi hh; have he := mem_antidiagonal.mp hi; have hv : i.1 ≠ v := by rintro e; exact hh (Prod.ext e (by dsimp; omega));
      simp [hv]
    exact fun he => (he (mem_antidiagonal.mpr (by dsimp;omega))).elim
  rename_i h; apply Finset.sum_eq_zero; intro i hi; have he := mem_antidiagonal.mp hi; simp [show i.1≠v by omega]

lemma starts (p : R) : push f (C p)= f p := by rw [← monomial_zero_eq_C_apply,push_mono,pow_zero,one_mul] -- inspect
private def ordersum (p : PowerSeries R) (n : ℕ) := ∑ i∈range (n+1), monomial i (coeff i p)
private lemma booked (p : PowerSeries R) (n : ℕ) : Through n (ordersum p n) p := by
  intro i hi; rw [ordersum,map_sum]; simp [coeff_monomial, Finset.mem_range,hi]

lemma onMul (p q : P) : push f (p*q) = push f p*push f q := by
  apply PowerSeries.ext; intro n; let a (i) := monomial i (coeff i p); let b (i) := monomial i (coeff i q); let S:=range (n+1)
  have h : push f (ordersum p n * ordersum q n) = push f (ordersum p n) * push f (ordersum q n) := by
    unfold ordersum; rw [map_sum, map_sum]; rw [Finset.sum_mul_sum,map_sum,Finset.sum_mul_sum];
    refine sum_congr rfl fun i hi=> ?_; rw [map_sum]; apply sum_congr rfl; intro j _; rw [monomial_mul_monomial,push_mono,push_mono,push_mono,map_mul,pow_add]; ring
  rw [← near_aux f ((booked p n).mul (booked q n)) n le_rfl,h]
  exact Through.mul (near_aux f (booked p n)) (near_aux f (booked q n)) n le_rfl

def throwTo : (PowerSeries R) →+* PowerSeries S where
  __ := push f
  map_one' := by change push f _=_; rw [← C.map_one,starts,map_one]
  map_mul' := onMul f
end mapCoeff
variable {I B : Type} (f : I → Channel B) (p : Channel I)
def replot : Channel I →+* Channel B := mapCoeff.throwTo (MvPolynomial.aeval f : Packet I →ₐ[ℂ] Channel B)
lemma replot_coeff (n) : coeff n (replot f p) = ∑ i∈ antidiagonal n, coeff i.2 (MvPolynomial.aeval f (coeff i.1 p)) := mapCoeff.push_coeff _ _ _
lemma replot_constant (p : Packet I) : replot f (C p)= MvPolynomial.aeval f p := by
  unfold replot mapCoeff.throwTo; change mapCoeff.push _ _=_; exact mapCoeff.starts (MvPolynomial.aeval f : Packet I →ₐ[ℂ] Channel B).toRingHom p
end YM.FormalOPE.RG10.Route
