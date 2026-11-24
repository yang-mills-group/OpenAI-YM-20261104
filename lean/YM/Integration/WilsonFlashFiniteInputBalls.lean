import YangMills.WilsonProof.NativeSupport.Commissioned259.Compare.Accounting

noncomputable section
namespace YM.FVA2.GradedFar.AppointedFlashBalls
open XSpace XSpace.Normalize XSpace.Structure1 Scale O.Score O.Enh Dframe
open YM.FVA2.GradedFar259 YM.FVA2.GradedFar259.Comparing
open scoped BigOperators Classical
variable {G : Gauge} {n m : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}

private theorem farBound (f : MLA G e) (v : Slots G e) {R : ℝ} (hR : 0 ≤ R)
    (hv : v ∈ Balls R G e) (A : BasisSlots G e → ℝ) (h : ∀ c, ‖f (word c)‖ ≤ A c) :
    ‖f v‖ ≤ ∑ c : BasisSlots G e, R^m * A c := by
  rw [word_sigma v f]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [smul_eq_mul, norm_mul]
  exact mul_le_mul (coord_price hR v hv c) (h c) (norm_nonneg _) (pow_nonneg hR _)

theorem response (f : Response G d e) (u : Slots G d) (v : Slots G e)
    {L R : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) (hu : u ∈ Balls L G d) (hv : v ∈ Balls R G e)
    (C : BasisSlots G d → BasisSlots G e → ℝ) (rate : ℝ)
    (h : ∀ b c, ‖f (word b) (word c)‖ ≤ C b c * rate) :
    ‖f u v‖ ≤ (∑ b : BasisSlots G d, ∑ c : BasisSlots G e, L^n * (R^m * C b c)) * rate := by
  have expand : f u v = ∑ b : BasisSlots G d, coordinates b u * f (word b) v := by
    rw [word_sigma u f]
    simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  rw [expand, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_mul]
  have hf := farBound (f (word b)) v hR hv (fun c => C b c * rate) (h b)
  refine (mul_le_mul (coord_price hL u hu b) hf (norm_nonneg _) (pow_nonneg hL _)).trans_eq ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

end YM.FVA2.GradedFar.AppointedFlashBalls
