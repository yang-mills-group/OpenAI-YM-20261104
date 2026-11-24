import YM.MSbar.Ballet.Palette

/-! Center the scalar part of the actual log-density discrepancy on its
physical small-field chart. The price of a displacement is its coordinate
one-norm, so moving a fixed number of coordinates incurs no volume factor. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical
open Lattice Push Push.Uniform MSbar MSbar.Lis MSbar.Ballet MSbar.Whisk
open scoped BigOperators Classical Topology

theorem centered_vacuum_bound {G : Gauge} {n : Side} {β : ℝ} {s p m : ℕ}
    {F : Positions (Primary n G) → ℝ} (T : Ticket β n F s p m)
    (hm : 4 ≤ m) (hw : 0 < Mosaic.vol β)
    (x : Positions (Primary n G)) (hx : x ∈ Metric.closedBall 0 (Mosaic.vol β)) :
    ‖F x - F 0‖ ≤ 5 * Mosaic.goalP β p / Mosaic.vol β * ∑ i, ‖x i‖ := by
  let w := Mosaic.vol β
  let a := Mosaic.αm β
  let B := Mosaic.goalP β p
  have ha : 0 ≤ a := by
    have : 0 < Mosaic.hatW β := (div_pos_iff_of_pos_right (by norm_num : (0 : ℝ) < 32)).mp hw
    exact zpow_nonneg this.le _
  have J := JetTab.levelAll hw ha T.grown T.rangeP hm le_rfl 0 (Nat.zero_le m)
  have price (i : Primary n G) : 1 ≤ Measuring.swipe (Measuring.chart n G) a s [i] := by
    calc
      1 = liftW a s 0 := by simp [liftW]
      _ ≤ _ := w_more (Nat.zero_le _) ha s
  have segment (t : ℝ) (ht : t ∈ Set.Icc 0 1) : t • x ∈ Metric.closedBall 0 w := by
    apply mem_closedBall_zero_iff.mpr
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg x) ht.2).trans (mem_closedBall_zero_iff.mp hx)
  have coordinate (y : Positions (Primary n G)) (hy : y ∈ Metric.closedBall 0 w)
      (i : Primary n G) : ‖fderiv ℝ F y (bolt i)‖ ≤ 5 * B / w := by
    have h := J.count hw y hy i
    change ‖fderiv ℝ F y (bolt i)‖ * Measuring.swipe (Measuring.chart n G) a s [i] ≤
      5 * B / w ^ (0+1) at h
    exact (le_mul_of_one_le_right (norm_nonneg _) (price i)).trans (by simpa only [Nat.zero_add, pow_one] using h)
  have directional (y : Positions (Primary n G)) (hy : y ∈ Metric.closedBall 0 w) :
      ‖fderiv ℝ F y x‖ ≤ 5 * B / w * ∑ i, ‖x i‖ := by
    calc
      ‖fderiv ℝ F y x‖ = ‖fderiv ℝ F y (∑ i, x i • bolt i)‖ :=
        congrArg (fun v => ‖fderiv ℝ F y v‖) (Lis.spiral x)
      _ ≤ ∑ i, ‖x i‖ * (5 * B / w) := by
        rw [map_sum]
        apply (norm_sum_le ..).trans
        exact Finset.sum_le_sum fun i _ => by
          rw [map_smul, norm_smul]
          exact mul_le_mul_of_nonneg_left (coordinate y hy i) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  let f := fun t : ℝ => F (t • x)
  have diff (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      HasDerivAt f (fderiv ℝ F (t • x) x) t := by
    have h : DifferentiableAt ℝ F (t • x) :=
      (T.grown _ (segment t ht)).differentiableAt (by simp)
    apply h.hasFDerivAt.comp_hasDerivAt
    simpa using (hasDerivAt_id' t).smul_const x
  have bound := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := f)
    (f' := fun t => fderiv ℝ F (t • x) x) (fun t ht => (diff t ht).hasDerivWithinAt)
    (fun t ht => directional _ (segment t (Set.Ico_subset_Icc_self ht)))
  simpa only [f, one_smul, zero_smul] using bound

end YM.Integration.FVA1Physical
