import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
/-!
# Separately cropped series

Here crop through p inclusive, and evaluate. The overrun identity exhibits *every*
mixed power term from the product outside that crop. In the price analysis they will
be bounded even though they are not in the individually-through-p OPE comparison of
formal series.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set PowerSeries
open scoped Topology BigOperators Classical

/-- Crop (inclusive p) then evaluate a formal series at real t. -/
def crop (p : ℕ) (t : ℝ) : PowerSeries ℂ →ₗ[ℂ] ℂ := ∑ k ∈ Finset.range (p+1),
  (t:ℂ)^k • coeff k
abbrev appointedH140Crop (p : ℕ) (t : ℝ) : PowerSeries ℂ →ₗ[ℂ] ℂ := crop p t
lemma crop_eq (p : ℕ) (t : ℝ) (f : PowerSeries ℂ) :
    crop p t f = ∑ k ∈ Finset.range (p+1), (t:ℂ)^k * coeff k f := by
  simp only [crop, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

def skipped (p : ℕ) := ((Finset.range (p+1)).product (Finset.range (p+1))).filter
  (fun x => ¬x.1+x.2 ≤ p)
lemma skipped_spec {p : ℕ} (x : ℕ×ℕ) (hx : x ∈ skipped p) :
    x.1 < p+1 ∧ x.2 < p+1 ∧ p+1 ≤ x.1 + x.2 := by
  simp only [skipped, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range] at hx
  omega

def overrun (p : ℕ) (t : ℝ) (f g : PowerSeries ℂ) :=
    ∑ x ∈ skipped p, (t:ℂ)^(x.1+x.2-(p+1)) * (coeff x.1 f * coeff x.2 g)

theorem separate (p : ℕ) (t : ℝ) (f g : PowerSeries ℂ) :
    crop p t f * crop p t g = crop p t (f*g) + (t:ℂ)^(p+1) * overrun p t f g := by
  let low (x : ℕ × ℕ) := x.1+x.2 ≤ p
  letI : DecidablePred low := fun i => Nat.decLe (i.1+i.2) p
  let S := Finset.range (p+1)
  let term (x : ℕ×ℕ) := (t:ℂ)^(x.1+x.2) * (coeff x.1 f * coeff x.2 g)
  have hu : (S.product S).filter low = S.biUnion (fun i => Finset.antidiagonal i) := by
    ext ⟨i,j⟩
    simp only [S, Finset.mem_range, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_biUnion,
      Finset.mem_antidiagonal, low]
    constructor
    · intro h; exact ⟨i+j, by omega, rfl⟩
    rintro ⟨k,hk,h⟩
    omega
  have hd : Set.PairwiseDisjoint (↑S) (fun i : ℕ => Finset.antidiagonal i) := by
    intro i _ j _ h; apply Finset.disjoint_left.mpr
    intro v hx hy; exact h ((Finset.mem_antidiagonal.mp hx).symm.trans (Finset.mem_antidiagonal.mp hy))
  have small : ∑ x ∈ (S.product S).filter low, term x = crop p t (f*g) := by
    rw [hu, Finset.sum_biUnion hd, crop_eq]
    simp_rw [coeff_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x hx => by
      simp only [term, Finset.mem_antidiagonal.mp hx]
  calc
    _ = ∑ x ∈ S.product S, term x := by
      rw [Finset.product_eq_sprod, Finset.sum_product, crop_eq, crop_eq, Finset.sum_mul]; simp_rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        unfold term; simp only [pow_add]; ring
    _ = ∑ x ∈ (S.product S).filter low, term x + ∑ x ∈ skipped p, term x :=
      (Finset.sum_filter_add_sum_filter_not _ low _).symm
    _ = _ := by
      rw [small, overrun, Finset.mul_sum, add_right_inj]
      exact Finset.sum_congr rfl fun x hx => by
        rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (skipped_spec x hx).2.2]

end YM.FVA2.GradedFar

namespace YM.FVA2.GradedFar
noncomputable section
open PowerSeries Finset
open scoped BigOperators

variable (p : ℕ) (t : ℝ) (f g : PowerSeries ℂ)

lemma crop_add : crop p t (f+g) = crop p t f + crop p t g := by
  simp only [crop_eq, map_add, mul_add, Finset.sum_add_distrib]
lemma crop_sub : crop p t (f-g) = crop p t f - crop p t g := by
  simp only [crop_eq, map_sub, mul_sub, Finset.sum_sub_distrib]
lemma crop_zero : crop p t 0 = 0 := by simp [crop_eq]
lemma crop_C_mul (z : ℂ) : crop p t (C z * f) = z * crop p t f := by
  simp only [crop_eq]
  simp_rw [coeff_C_mul, mul_left_comm ((t:ℂ)^_) z]
  rw [Finset.mul_sum]
lemma crop_sum {ι : Type*} (s : Finset ι) (v : ι → PowerSeries ℂ) :
    crop p t (∑ i ∈ s, v i) = ∑ i ∈ s, crop p t (v i) := by
  simp_rw [crop_eq, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Cross terms above the crop, from evaluating each factor through the crop. -/
def pairsAbove (p : ℕ) : Finset (ℕ × ℕ) :=
  ((range (p+1)) ×ˢ (range (p+1))).filter (fun q => p < q.1+q.2)
@[simp] lemma mem_pairsAbove (q : ℕ × ℕ) :
    q ∈ pairsAbove p ↔ (q.1 ≤ p ∧ q.2 ≤ p) ∧ p < q.1+q.2 := by
  simp only [pairsAbove, mem_filter, mem_product, mem_range_succ_iff]

def cross (t : ℝ) (f g : PowerSeries ℂ) (q : ℕ × ℕ) : ℂ :=
  (t:ℂ)^(q.1+q.2) * (coeff q.1 f * coeff q.2 g)

/-- Accounting for *all* pairs in the product. -/
theorem crop_mul : crop p t f * crop p t g =
    crop p t (f*g) + ∑ q ∈ pairsAbove p, cross t f g q := by
  let S := (range (p+1)) ×ˢ (range (p+1))
  have expand : crop p t f * crop p t g = ∑ q ∈ S, cross t f g q := by
    simp only [crop_eq, S]
    rw [sum_product, Finset.sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun j _ => ?_
    dsimp only [cross]
    rw [pow_add]
    ac_rfl
  have low : crop p t (f*g) = ∑ q ∈ S with q.1+q.2 ∈ range (p+1), cross t f g q := by
    rw [← sum_fiberwise_eq_sum_filter S (range (p+1)) (fun q => q.1+q.2)]
    simp only [crop_eq]
    refine sum_congr rfl fun k hk => ?_
    have hk := mem_range_succ_iff.mp hk
    rw [coeff_mul, Finset.mul_sum]
    have he : S.filter (fun q => q.1+q.2=k) = antidiagonal k := by
      ext q
      simp only [S, mem_filter, mem_product, mem_range_succ_iff, mem_antidiagonal]
      omega
    rw [he]
    refine sum_congr rfl fun q hq => ?_
    rw [cross, mem_antidiagonal.mp hq]
  rw [expand, low, ← sum_filter_add_sum_filter_not S (fun q => q.1+q.2 ∈ range (p+1))]
  rcongr _
  simp

/-- Exact finite polynomial carrying the invoice after a factor of degree
`p+1` has been removed. -/
def invoice (p : ℕ) (t : ℝ) (f g : PowerSeries ℂ) : ℂ :=
  ∑ q ∈ pairsAbove p,
    (t:ℂ)^(q.1+q.2-(p+1)) * (coeff q.1 f * coeff q.2 g)

theorem crop_invoice : crop p t f * crop p t g = crop p t (f*g) + (t:ℂ)^(p+1)*invoice p t f g := by
  rw [crop_mul, invoice, Finset.mul_sum]
  refine congrArg (_+·) (sum_congr rfl fun q hq => ?_)
  have he := ((mem_pairsAbove p q).mp hq).2
  rw [cross, ← mul_assoc ((t:ℂ)^(p+1)), ← pow_add, show p+1 + (q.1+q.2-(p+1)) = q.1+q.2 by omega]

end
end YM.FVA2.GradedFar
