import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Analysis.Complex.Basic

/-!
# Through-p crops (t fixed in each evaluation)

This is finite algebra. There will be two such operations in the (formal half
of the) NearFarDelta estimate, not to be confused: crop one formal value (legs
already converted) or multiply **separate** crops.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open PowerSeries Finset
open scoped Polynomial

/-- Evaluate the crop through (including) p. When a value is multilinear on
series legs form the series *before* this operation. -/
def filedCrop122 (p : ℕ) (z : ℂ) (F : PowerSeries ℂ) : ℂ := (trunc (p+1) F).eval z

variable {ι : Type*} (p : ℕ) (z : ℂ) (F G : PowerSeries ℂ)

lemma filedCropEq122 : filedCrop122 p z F = ∑ i ∈ range (p+1), coeff i F * z^i :=
  eval₂_trunc_eq_sum_range z (RingHom.id ℂ) _ F

lemma filedCrop122_C_mul (c : ℂ) : filedCrop122 p z (C c * F) = c * filedCrop122 p z F := by
  simp [filedCrop122]

lemma filedCrop122_sum (s : Finset ι) (f : ι → PowerSeries ℂ) :
    filedCrop122 p z (∑ i ∈ s, f i) = ∑ i ∈ s, filedCrop122 p z (f i) := by
  simp only [filedCrop122, map_sum, Polynomial.eval_finsetSum]

lemma filedCrop122_add : filedCrop122 p z (F + G) = filedCrop122 p z F + filedCrop122 p z G := by
  simp only [filedCrop122, map_add, Polynomial.eval_add]

lemma filedCrop122_sub : filedCrop122 p z (F - G) = filedCrop122 p z F - filedCrop122 p z G := by
  simp only [filedCrop122, map_sub, Polynomial.eval_sub]

/-- Rectangle of indices of two separate through-p crops. -/
def rectangle (p : ℕ) : Finset (ℕ × ℕ) := (range (p+1)) ×ˢ (range (p+1))

lemma in_rectangle {i : ℕ × ℕ} : i ∈ rectangle p ↔ i.1 ≤ p ∧ i.2 ≤ p := by
  simp [rectangle]

/-- All the excess degrees, even from positive orders of replacement fields.
Denumerated with their actual coupling power (here after removing a common
factor `z^(p+1)`). -/
def excess (p : ℕ) : Finset (ℕ × ℕ) := {ij ∈ rectangle p | ¬ ij.1+ij.2 ≤ p}
def bill (p : ℕ) (z : ℂ) (F G : PowerSeries ℂ) : ℂ :=
  ∑ ij ∈ excess p, coeff ij.1 F * coeff ij.2 G * z^(ij.1+ij.2-(p+1))

/-- Therefore even in finite formal calculations the price of using separately
estimated coefficients must pay this sum. -/
theorem separate_crop_exact : filedCrop122 p z F * filedCrop122 p z G =
    filedCrop122 p z (F*G) + bill p z F G * z^(p+1) := by
  let weight (j : ℕ × ℕ) := coeff j.1 F * coeff j.2 G * z^(j.1+j.2)
  have low : {ij ∈ rectangle p | ij.1+ij.2 ≤ p} = (range (p+1)).biUnion antidiagonal := by
    ext ij
    simp only [mem_filter, in_rectangle, mem_biUnion, mem_range, mem_antidiagonal]
    constructor
    · intro h; exact ⟨ij.1+ij.2, by omega, rfl⟩
    · rintro ⟨i,hi,hj⟩; omega
  have disjoint : (↑(range (p+1)) : Set ℕ).PairwiseDisjoint antidiagonal := by
    intro i _ j _ h
    exact disjoint_left.mpr (fun s hx hy => h ((mem_antidiagonal.mp hx).symm.trans (mem_antidiagonal.mp hy)))
  calc
    _ = ∑ i ∈ rectangle p, weight i := by
      rw [filedCropEq122, filedCropEq122, rectangle, sum_mul_sum, sum_product]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => (by dsimp only [weight]; rw [pow_add]; ring)
    _ = (∑ i ∈ {ij ∈ rectangle p | ij.1+ij.2 ≤ p}, weight i) + ∑ i ∈ excess p, weight i :=
      (sum_filter_add_sum_filter_not ..).symm
    _ = _ := by
      congr 1
      · rw [low, sum_biUnion disjoint, filedCropEq122]
        apply sum_congr rfl; intro n _; rw [coeff_mul, sum_mul]
        exact sum_congr rfl fun i hi => by dsimp only [weight]; rw [mem_antidiagonal.mp hi]
      · rw [bill, sum_mul]
        apply sum_congr rfl; intro i hi; rw [mul_assoc, ← pow_add]
        have he : p+1 ≤ i.1+i.2 := Nat.succ_le_of_lt (Nat.lt_of_not_ge (mem_filter.mp hi).2)
        rw [Nat.sub_add_cancel he]

end YM.FVA2.GradedFar
