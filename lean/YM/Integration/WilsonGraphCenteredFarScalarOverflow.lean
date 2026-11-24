import YM.Integration.WilsonGraphCenteredFarHeaterSubstitution

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedScalarOverflow

open Finset PowerSeries Continuation
open scoped BigOperators Classical

def mass (p : ℕ) (A : PowerSeries ℂ) : ℝ := ∑ i ∈ range (p+1), ‖coeff i A‖

private abbrev box (p : ℕ) := (range (p+1)) ×ˢ (range (p+1))
private abbrev order (q : ℕ × ℕ) := q.1+q.2
private def term (t : ℝ) (A B : PowerSeries ℂ) (q : ℕ × ℕ) : ℂ :=
  (t:ℂ)^(order q) * (coeff q.1 A * coeff q.2 B)

private theorem fibers {E : Type} [AddCommMonoid E] (p : ℕ) (F : ℕ × ℕ → E) :
    (∑ j ∈ range (p+1), ∑ q ∈ antidiagonal j, F q) =
      ∑ q ∈ box p with order q ∈ range (p+1), F q := by
  rw [← sum_fiberwise_eq_sum_filter (box p) (range (p+1)) order]
  apply sum_congr rfl
  intro j hj
  have top := mem_range_succ_iff.mp hj
  have fiber : (box p).filter (fun q => order q = j) = antidiagonal j := by
    ext q
    simp only [box, order, mem_filter, mem_product, mem_range_succ_iff,
      HasAntidiagonal.mem_antidiagonal]
    omega
  rw [fiber]

private theorem low (p : ℕ) (t : ℝ) (A B : PowerSeries ℂ) :
    crop p t (A * B) = ∑ q ∈ box p with order q ∈ range (p+1), term t A B q := by
  rw [← fibers, YM.FVA2.GradedFar.crop_eq]
  apply sum_congr rfl
  intro j _
  rw [coeff_mul, Finset.mul_sum]
  apply sum_congr rfl
  intro q hq
  rw [term, order, HasAntidiagonal.mem_antidiagonal.mp hq]

/-- The finite evaluation pays exactly for the Cauchy terms whose total order exceeds p. -/
theorem product (p : ℕ) (t : ℝ) (A B : PowerSeries ℂ) :
    crop p t A * crop p t B - crop p t (A * B) =
      ∑ q ∈ box p with order q ∉ range (p+1), term t A B q := by
  have expand : crop p t A * crop p t B = ∑ q ∈ box p, term t A B q := by
    simp only [YM.FVA2.GradedFar.crop_eq, box]
    rw [sum_product, Finset.sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun j _ => ?_
    simp only [term,order,pow_add]
    ring
  rw [expand, low, ←sum_filter_add_sum_filter_not (box p) (fun q => order q ∈ range (p+1))]
  abel

private theorem boxMass (p : ℕ) (A B : PowerSeries ℂ) :
    (∑ q ∈ box p, ‖coeff q.1 A‖ * ‖coeff q.2 B‖) = mass p A * mass p B := by
  unfold box mass
  rw [sum_product, Finset.sum_mul]
  refine sum_congr rfl fun i _ => ?_
  exact (Finset.mul_sum (range (p+1)) (fun j => ‖coeff j B‖) (‖coeff i A‖)).symm

theorem massProduct (p : ℕ) (A B : PowerSeries ℂ) :
    mass p (A * B) ≤ mass p A * mass p B := by
  rw [← boxMass]
  calc mass p (A*B) ≤ ∑ j ∈ range (p+1), ∑ q ∈ antidiagonal j, ‖coeff q.1 A‖ * ‖coeff q.2 B‖ := by
         unfold mass
         refine sum_le_sum fun j _ => ?_
         rw [coeff_mul]
         simpa only [norm_mul] using (norm_sum_le (antidiagonal j) (fun q => coeff q.1 A * coeff q.2 B))
       _ = _ := fibers _ _
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem normCrop (p : ℕ) (t : ℝ) (A : PowerSeries ℂ) (ht : |t| ≤ 1) :
    ‖crop p t A‖ ≤ mass p A := by
  simp only [YM.FVA2.GradedFar.crop_eq, mass]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (abs_nonneg _) ht)

theorem productPrice (p : ℕ) (t : ℝ) (A B : PowerSeries ℂ) (ht : |t| ≤ 1) :
    ‖crop p t A * crop p t B - crop p t (A*B)‖ ≤ |t|^(p+1) * (mass p A * mass p B) := by
  rw [product, ←boxMass]
  let hi := (box p).filter (fun q => order q ∉ range (p+1))
  calc ‖∑ q ∈ hi, term t A B q‖ ≤ ∑ q ∈ hi, ‖term t A B q‖ := norm_sum_le _ _
       _ ≤ ∑ q ∈ hi, |t|^(p+1) * (‖coeff q.1 A‖ * ‖coeff q.2 B‖) := by
         refine sum_le_sum fun q hq => ?_
         have bound : p+1 ≤ order q := by simpa only [mem_range,not_lt] using (mem_filter.mp hq).2
         rw [term, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
         exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (abs_nonneg _) ht bound) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
       _ = |t|^(p+1) * ∑ q ∈ hi, ‖coeff q.1 A‖ * ‖coeff q.2 B‖ := (Finset.mul_sum ..).symm
       _ ≤ _ := mul_le_mul_of_nonneg_left
         (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))) (pow_nonneg (abs_nonneg _) _)

/-- A fixed kernel coefficient series with one series for each of its two true field slots. -/
theorem threePrice (p : ℕ) (t : ℝ) (A B F : PowerSeries ℂ) (ht : |t| ≤ 1) :
    ‖crop p t A * crop p t B * crop p t F - crop p t (A*B*F)‖ ≤
      2 * |t|^(p+1) * (mass p A * mass p B * mass p F) := by
  let x := crop p t A * crop p t B - crop p t (A*B)
  let z := crop p t (A*B) * crop p t F - crop p t (A*B*F)
  have regroup : crop p t A * crop p t B * crop p t F - crop p t (A*B*F) = x * crop p t F + z := by
    dsimp only [x,z]; ring
  have hF : 0 ≤ mass p F := sum_nonneg (fun _ _ => norm_nonneg _)
  have hAB : 0 ≤ mass p A * mass p B := mul_nonneg (sum_nonneg fun _ _ => norm_nonneg _) (sum_nonneg fun _ _ => norm_nonneg _)
  rw [regroup]
  refine (norm_add_le ..).trans ?_
  rw [norm_mul]
  have e1 := mul_le_mul (productPrice p t A B ht) (normCrop p t F ht) (norm_nonneg _) (mul_nonneg (pow_nonneg (abs_nonneg _) _) hAB)
  have e2 := (productPrice p t (A*B) F ht).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (massProduct p A B) hF) (pow_nonneg (abs_nonneg _) _))
  exact (add_le_add e1 e2).trans_eq (by ring)

end YM.FVA2.GradedFar.AppointedScalarOverflow
