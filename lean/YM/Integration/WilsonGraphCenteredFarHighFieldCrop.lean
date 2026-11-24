import YM.Integration.WilsonGraphCenteredFarBilinearPrice

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedHighFieldCrop

open PowerSeries Finset Continuation Growth
open Register MS MS.Native MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point AppointedScalarOverflow
open scoped BigOperators Classical

private theorem massNonneg (k : ℕ) (A : PowerSeries ℂ) : 0 ≤ mass k A :=
  sum_nonneg fun _ _ => norm_nonneg _

theorem massMono {p k : ℕ} (hpk : p ≤ k) (A : PowerSeries ℂ) : mass p A ≤ mass k A :=
  sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.succ_le_succ hpk))
    (fun _ _ _ => norm_nonneg _)

theorem tail {p k : ℕ} (hpk : p ≤ k) (t : ℝ) (A : PowerSeries ℂ) (ht : |t| ≤ 1) :
    ‖crop k t A - crop p t A‖ ≤ |t|^(p+1) * mass k A := by
  let hi := (range (k+1)).filter (fun i => i ∉ range (p+1))
  have keep : (range (k+1)).filter (fun i => i ∈ range (p+1)) = range (p+1) := by
    ext i
    simp only [mem_filter,mem_range]
    omega
  have split : crop k t A - crop p t A = ∑ i ∈ hi, (t:ℂ)^i * coeff i A := by
    simp only [YM.FVA2.GradedFar.crop_eq, hi]
    rw [←sum_filter_add_sum_filter_not (range (k+1)) (fun i => i ∈ range (p+1)),keep]
    abel
  rw [split]
  calc ‖∑ i ∈ hi, (t:ℂ)^i * coeff i A‖ ≤ ∑ i ∈ hi, ‖(t:ℂ)^i * coeff i A‖ := norm_sum_le _ _
       _ ≤ ∑ i ∈ hi, |t|^(p+1) * ‖coeff i A‖ := by
         refine sum_le_sum fun i h => ?_
         have order : p+1 ≤ i := by simpa only [mem_range,not_lt] using (mem_filter.mp h).2
         rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
         exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (abs_nonneg _) ht order) (norm_nonneg _)
       _ = |t|^(p+1) * ∑ i ∈ hi, ‖coeff i A‖ := (Finset.mul_sum ..).symm
       _ ≤ _ := mul_le_mul_of_nonneg_left
         (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => norm_nonneg _)) (pow_nonneg (abs_nonneg _) _)

/-- The field matrices may be evaluated to any higher order selected by the physical
transport estimate. Only the actual correlation predictor is cut at p. -/
theorem scalar {p k : ℕ} (hpk : p ≤ k) (t : ℝ) (A B F : PowerSeries ℂ) (ht : |t| ≤ 1) :
    ‖crop k t A * crop k t B * crop p t F - crop p t (A*B*F)‖ ≤
      4 * |t|^(p+1) * (mass k A * mass k B * mass p F) := by
  let e := |t|^(p+1)
  have he : 0 ≤ e := pow_nonneg (abs_nonneg _) _
  have hA := massNonneg k A
  have hB := massNonneg k B
  have hF := massNonneg p F
  let i := (crop k t A-crop p t A)*crop k t B*crop p t F
  let j := crop p t A*(crop k t B-crop p t B)*crop p t F
  let z := crop p t A*crop p t B*crop p t F-crop p t (A*B*F)
  have split : crop k t A*crop k t B*crop p t F-crop p t (A*B*F) = i+j+z := by dsimp only [i,j,z]; ring
  have ia := mul_le_mul (tail hpk t A ht) (normCrop k t B ht) (norm_nonneg _) (mul_nonneg he hA)
  have ib := mul_le_mul ia (normCrop p t F ht) (norm_nonneg _) (mul_nonneg (mul_nonneg he hA) hB)
  have ii : ‖i‖ ≤ e*(mass k A*mass k B*mass p F) := by
    simpa only [i,norm_mul,e,mul_assoc] using ib
  have ja := mul_le_mul ((normCrop p t A ht).trans (massMono hpk A)) (tail hpk t B ht) (norm_nonneg _) hA
  have jb := mul_le_mul ja (normCrop p t F ht) (norm_nonneg _) (mul_nonneg hA (mul_nonneg he hB))
  have jj : ‖j‖ ≤ e*(mass k A*mass k B*mass p F) := by
    dsimp only [j]; simp only [norm_mul]
    exact jb.trans_eq (by dsimp only [e]; ring)
  have ab := mul_le_mul (massMono hpk A) (massMono hpk B) (massNonneg p B) hA
  have zz : ‖z‖ ≤ 2*e*(mass k A*mass k B*mass p F) := (threePrice p t A B F ht).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ab hF) (mul_nonneg (by norm_num) he))
  rw [split]
  have bound := (norm_add_le (i+j) z).trans (add_le_add (norm_add_le i j) (le_refl ‖z‖))
  exact bound.trans ((add_le_add (add_le_add ii jj) zz).trans_eq (by dsimp only [e];ring))

variable {G : Gauge} (N : Register.WilsonPrescription G)

def bookValue (h p k : ℕ) (x : Scale.Stage 2) (A B : Guard G h) (u v : Sec G h) (t : ℝ) : ℂ :=
  ∑ c : Fin 2 → Dime G h, crop k t (tax A u (c 0)) * crop k t (tax B v (c 1)) *
    crop p t (Reg.Point.story (book N h 2 x) (fun i => dime G h (c i)))

theorem expense (h p k : ℕ) (hpk : p ≤ k) (x : Scale.Stage 2) (A B : Guard G h)
    (u v : Sec G h) (t : ℝ) (ht : |t| ≤ 1) :
    ‖bookValue N h p k x A B u v t - crop p t (AppointedBilinearCauchy.full N h x A B u v)‖ ≤
      4 * |t|^(p+1) * ∑ c : Fin 2 → Dime G h,
        mass k (tax A u (c 0)) * mass k (tax B v (c 1)) *
          mass p (Reg.Point.story (book N h 2 x) (fun i => dime G h (c i))) := by
  unfold bookValue AppointedBilinearCauchy.full
  have commute {I : Type} [Fintype I] (U : I → PowerSeries ℂ) : crop p t (∑ i,U i) = ∑ i,crop p t (U i) := by
    exact YM.FVA2.GradedFar.crop_sum p t Finset.univ U
  rw [commute,←Finset.sum_sub_distrib,Finset.mul_sum]
  exact (norm_sum_le _ _).trans (sum_le_sum fun c _ => scalar hpk t _ _ _ ht)

end YM.FVA2.GradedFar.AppointedHighFieldCrop
