import YM.Push.FREE_RESOLVENT.Layout

/-! Reconstruction of a normed-output form on the genuine coarse field
coordinates, with no torus-cardinality factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalCoarseFieldBasis
open Function Lattice Wilson RG FreeResolvent FreeResolvent.Affine
open scoped Classical BigOperators

variable {G : Gauge} {c : Side} {j : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Every original coarse coefficient includes its full Lie color. -/
theorem expand (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Vec G c 1) X)
    (B : Fin j→Vec G c 1) :
    T B=∑ l : Fin j→ raw G c, (∏ i,B i (l i)) • T (ray G c ∘ l) := by
  classical
  have e (i : Fin j) : B i=∑ k : raw G c, B i k • ray G c k := by
    ext k
    simp [ray,Pi.single_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_ite]
  calc
    T B = T (fun i => ∑ k, B i k • ray G c k) := by congr 1; funext i; exact e i
    _ = ∑ l : Fin j→ raw G c, T (fun i => B i (l i) • ray G c (l i)) := by
      rw [T.map_sum (fun i k => B i k • ray G c k)]
    _ = _ := Finset.sum_congr rfl fun l _ => T.map_smul_univ (fun i => B i (l i)) (ray G c ∘ l)

/-- The zero-order right hand side has one term, coming from the unique
empty input word. The bound requires no positive-order assumption. -/
theorem norm_le (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Vec G c 1) X) :
    ‖T‖≤∑ l : Fin j→ raw G c, ‖T (ray G c ∘ l)‖ := by
  classical
  refine ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) ?_
  intro B
  rw [expand T B,Finset.sum_mul]
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum
  intro l _
  rw [norm_smul,Real.norm_eq_abs,Finset.abs_prod]
  have hc : (∏ i,|B i (l i)|)≤∏ i,‖B i‖ :=
    Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (B i) (l i)
  exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (mul_comm ..)

end YM.Integration.PhysicalCoarseFieldBasis
end
