import YM.RG.Push

/-! Coupling variation of the observed links in the original Wilson block.
The cardinality entering the likelihood ratio is the observed set's size. -/
noncomputable section
namespace YM.Integration.WilsonKernelCoupling
open YM MeasureTheory Lattice Wilson RG Set
open scoped BigOperators
variable {c f : Side} (S : StepData c f) {G : Gauge}

def change (b a : ℝ) : ℝ := |a-b| * |S.kernel.penalty| * 2

theorem change_symm (b a : ℝ) : change S b a = change S a b := by
  unfold change
  rw [abs_sub_comm a b]

/-- The unnormalized one-link kernel uses the actual gauge price in [0,2]. -/
theorem weight_le (b a : ℝ) (v : G.El) :
    S.penaltyWeight b v ≤ Real.exp (change S b a) * S.penaltyWeight a v := by
  have h : (a-b) * S.kernel.penalty * G.price v ≤ change S b a := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (G.price_range v).1]
    exact mul_le_mul_of_nonneg_left (G.price_range v).2
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have he : S.penaltyWeight b v =
      Real.exp ((a-b) * S.kernel.penalty * G.price v) * S.penaltyWeight a v := by
    unfold StepData.penaltyWeight
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h) (Real.exp_pos _).le

theorem normalizer_le (b a : ℝ) :
    S.penaltyZ b G ≤ Real.exp (change S b a) * S.penaltyZ a G := by
  let hI (t : ℝ) : Integrable (S.penaltyWeight (G := G) t) G.probHaar :=
    (S.penaltyWeight_cont _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold StepData.penaltyZ
  rw [← integral_const_mul]
  exact integral_mono (hI b) ((hI a).const_mul _) (fun v => weight_le S b a v)

def link (b : ℝ) (q v : G.El) : ℝ := S.penaltyWeight b (v*q⁻¹) / S.penaltyZ b G

theorem link_pos (b : ℝ) (q v : G.El) : 0 < link S b q v :=
  div_pos (Real.exp_pos _) (S.penaltyZ_pos b)

theorem link_mass (b : ℝ) (q : G.El) : (∫ v, link S b q v ∂G.probHaar) = 1 := by
  have h := (measurePreserving_mul_right G.probHaar q⁻¹).integral_comp
    ((Homeomorph.mulRight q⁻¹).measurableEmbedding) (S.penaltyWeight b)
  unfold link
  rw [integral_div, h, ← StepData.penaltyZ, div_self (S.penaltyZ_pos b).ne']

/-- Uniform in the predicted link and observed group element. -/
theorem link_le (b a : ℝ) (q v : G.El) :
    link S b q v ≤ Real.exp (2 * change S b a) * link S a q v := by
  have hz := normalizer_le (G := G) S a b
  rw [change_symm S a b] at hz
  unfold link
  rw [← mul_div_assoc, div_le_div_iff₀ (S.penaltyZ_pos b) (S.penaltyZ_pos a)]
  calc
    _ ≤ (Real.exp (change S b a) * S.penaltyWeight a (v*q⁻¹)) *
        (Real.exp (change S b a) * S.penaltyZ b G) :=
      mul_le_mul (weight_le S b a _) hz (S.penaltyZ_pos a).le
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = _ := by rw [two_mul, Real.exp_add]; ring

/-- The finite likelihood after integrating the unobserved normalized links. -/
def marginal (A : Finset (Edge (Site c))) (b : ℝ) (U : Config G f) (x : (i : A) → G.El) : ℝ :=
  ∑ t, S.likelihood U t * ∏ i : A, link S b (S.prediction U t i.val) (x i)

/-- All branches use the same local bound and their original weights. -/
theorem marginal_le (A : Finset (Edge (Site c))) (b a : ℝ) (U : Config G f) (x : (i : A) → G.El) :
    marginal S A b U x ≤ (Real.exp (2 * change S b a))^A.card * marginal S A a U x := by
  unfold marginal
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  let v (i : A) := S.prediction U t i.val
  have h : (∏ i : A, link S b (v i) (x i)) ≤
      ∏ i : A, Real.exp (2*change S b a) * link S a (v i) (x i) :=
    Finset.prod_le_prod (fun i _ => (link_pos S b _ _).le) (fun i _ => link_le S b a _ _)
  rw [Finset.prod_mul_distrib] at h
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe] at h
  calc
    _ ≤ S.likelihood U t * ((Real.exp (2*change S b a))^A.card * ∏ i : A, link S a (v i) (x i)) :=
      mul_le_mul_of_nonneg_left h (S.likelihood_pos U t)
    _ = _ := by dsimp only [v]; ring

end YM.Integration.WilsonKernelCoupling
