import YM.Integration.WilsonLocalKernelPairing

/-! Exact joint Laplace transforms of the observed Wilson link prices under the
original conditional Haar block, retaining the selected prediction in each branch. -/
noncomputable section
namespace YM.Integration.WilsonLocalKernelLaplace
open YM RG Lattice Wilson MeasureTheory WilsonKernelCoupling
open scoped BigOperators
variable {c f : Side} (S : StepData c f) {G : Gauge}

def tilt (A : Finset (Edge (Site c))) (b : ℝ) (a : A → ℝ) (Q : Config G c) (x : A → G.El) : ℝ :=
  ∏ i : A, S.penaltyWeight (a i-b) (x i * (Q i.val)⁻¹)

theorem shifted (b a : ℝ) (q v : G.El) :
    link S b q v * S.penaltyWeight (a-b) (v*q⁻¹) =
      (S.penaltyZ a G / S.penaltyZ b G) * link S a q v := by
  have hw : S.penaltyWeight b (v*q⁻¹) * S.penaltyWeight (a-b) (v*q⁻¹) =
      S.penaltyWeight a (v*q⁻¹) := by
    unfold StepData.penaltyWeight
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (S.penaltyWeight b (v*q⁻¹) * S.penaltyWeight (a-b) (v*q⁻¹)) / S.penaltyZ b G := by unfold link; ring
    _ = _ := by rw [hw]; unfold link; field_simp [(S.penaltyZ_pos a).ne', (S.penaltyZ_pos b).ne']

theorem measured (A : Finset (Edge (Site c))) (b : ℝ) (a : A → ℝ) (Q : Config G c) :
    (∫ V, S.noise b Q V * tilt S A b a Q (readLinks A V) ∂prior G c) =
      ∏ i : A, S.penaltyZ (a i) G / S.penaltyZ b G := by
  classical
  let L (i : A) (v : G.El) := link S b (Q i.val) v * S.penaltyWeight (a i-b) (v*(Q i.val)⁻¹)
  calc
    _ = ∫ x, branch S A b Q x * tilt S A b a Q x ∂(Measure.pi fun _ : A => G.probHaar) := by
      simpa only [smul_eq_mul] using noise_pairing S A b Q (tilt S A b a Q)
    _ = ∫ x, ∏ i : A, L i (x i) ∂(Measure.pi fun _ : A => G.probHaar) := by
      apply integral_congr_ae
      filter_upwards with x
      exact Finset.prod_mul_distrib.symm
    _ = ∏ i : A, ∫ v, L i v ∂G.probHaar := integral_fintype_prod_eq_prod L
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      unfold L
      simp_rw [shifted]
      rw [integral_const_mul, link_mass, mul_one]

theorem joint (h : S.patch.Branches S.kernel G) (A : Finset (Edge (Site c)))
    (b : ℝ) (a : A → ℝ) (U : Config G f) :
    (∑ z, S.likelihood U z * ∫ V, S.noise b (S.prediction U z) V *
      tilt S A b a (S.prediction U z) (readLinks A V) ∂prior G c) =
      ∏ i : A, S.penaltyZ (a i) G / S.penaltyZ b G := by
  simp_rw [measured]
  rw [← Finset.sum_mul, S.chosen h, one_mul]

end YM.Integration.WilsonLocalKernelLaplace
