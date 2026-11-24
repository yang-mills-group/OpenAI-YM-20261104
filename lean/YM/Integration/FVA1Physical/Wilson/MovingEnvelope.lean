import YM.RGComparison.Core16.Savings

/-! Extend an all-order small-coupling price when the physical expression
has a uniform bound on each interval bounded away from zero. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Set PertExtension PertExtension.Series PertExtension.Series.Tested
open scoped Classical Topology

theorem positive_price {f : ℝ → ℝ} {a : ℕ → ℝ} (h : Aspiration f a)
    (bounded : ∀ s > (0:ℝ), ∃ M : ℝ, 0 ≤ M ∧ ∀ g, s ≤ g → ‖f g‖ ≤ M) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g > (0:ℝ), ‖f g - peval a r g‖ ≤ C*g^(r+1) := by
  obtain ⟨B,hB,small⟩ := h r
  rw [eventually_nhdsWithin_iff] at small
  obtain ⟨s,hs,inside⟩ := Metric.mem_nhds_iff.mp small
  obtain ⟨M,hM,large⟩ := bounded s hs
  let A i := ‖a i‖ * s⁻¹^(r+1-i)
  let K := ∑ i ∈ Finset.range (r+1), A i
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (pow_nonneg (inv_nonneg.mpr hs.le) _)
  let E := M/s^(r+1) + K
  have hE : 0 ≤ E := add_nonneg (div_nonneg hM (pow_nonneg hs.le _)) hK
  refine ⟨B+E,add_nonneg hB hE,fun g hg => ?_⟩
  by_cases ht : g < s
  · have lo := inside (show g ∈ Metric.ball (0:ℝ) s by simpa [abs_of_pos hg] using ht) hg
    exact lo.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hE) (pow_nonneg hg.le _))
  have H := le_of_not_gt ht
  have rough : M ≤ M/s^(r+1)*g^(r+1) := by
    calc
      M = M/s^(r+1)*s^(r+1) := (div_mul_cancel₀ _ (pow_pos hs _).ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le H _) (div_nonneg hM (pow_nonneg hs.le _))
  have poly : ‖peval a r g‖ ≤ K*g^(r+1) := by
    unfold peval Zone.eval K
    rw [Finset.sum_mul]
    apply (norm_sum_le ..).trans (Finset.sum_le_sum ?_)
    intro i hi
    have hix := Finset.mem_range.mp hi
    have hp : g^i ≤ g^(r+1)*s⁻¹^(r+1-i) := by
      apply le_of_mul_le_mul_right (a:=s^(r+1-i)) ?_ (pow_pos hs _)
      rw [mul_assoc,inv_pow,inv_mul_cancel₀ (pow_pos hs _).ne',mul_one]
      refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le H _) (pow_nonneg hg.le _)).trans_eq ?_
      rw [← pow_add,show i+(r+1-i)=r+1 by omega]
    rw [norm_smul,Real.norm_of_nonneg (pow_nonneg hg.le _)]
    exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans_eq (by dsimp [A]; ring)
  exact (norm_sub_le ..).trans (((add_le_add ((large g H).trans rough) poly).trans_eq (add_mul ..).symm).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB) (pow_nonneg hg.le _)))

end YM.Integration.FVA1Physical.Wilson
