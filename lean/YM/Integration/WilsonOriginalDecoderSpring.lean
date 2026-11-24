import YM.Integration.WilsonOriginalFiledClearHearing

/-! A relative price for changing the retained field on the genuine last
Wilson edge. Each changed link is charged once. The estimate is uniform
in the fine field and every original predictor choice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalDecoderSpring
open Function Filter Finset MeasureTheory Lattice Wilson RG Pressure Push.BetaTransport
open scoped Classical BigOperators
variable {G : Gauge} {c f : Side}

theorem price (v u : G.El) : |G.price (v*u)-G.price u| ≤ 2*G.chord v := by
  have upper := G.chord_triangle v u
  have lower := G.chord_triangle v⁻¹ (v*u)
  simp only [inv_mul_cancel_left,Gauge.chord_inv] at lower
  have dist : |G.chord (v*u)-G.chord u| ≤ G.chord v :=
    abs_le.mpr ⟨by linarith only [lower],by linarith only [upper]⟩
  have sum : |G.chord (v*u)+G.chord u| ≤ 4 := by
    rw [abs_of_nonneg (add_nonneg (G.chord_nonneg _) (G.chord_nonneg _))]
    linarith only [G.chord_le_two (v*u),G.chord_le_two u]
  have eqn : 2*(G.price (v*u)-G.price u) = (G.chord (v*u)-G.chord u)*(G.chord (v*u)+G.chord u) := by
    nlinarith only [G.chord_price (v*u),G.chord_price u]
  have bound:=mul_le_mul dist sum (abs_nonneg _) (G.chord_nonneg _)
  rw [←abs_mul,←eqn,abs_mul,abs_of_nonneg (by norm_num : 0≤(2:ℝ))] at bound
  linarith only [bound]

def bill (S : StepData c f) (β : ℝ) (V : Config G c) : ℝ :=
  |β| * (2*S.kernel.penalty*∑ b : Bond c, G.chord (V b))

private theorem energy (S : StepData c f) (Q V : Config G c) :
    |noiseEnergy S Q V-noiseEnergy S Q 1| ≤ 2*S.kernel.penalty*∑ b : Bond c,G.chord (V b) := by
  unfold noiseEnergy linkEnergy
  simp only [Pi.one_apply,one_mul,←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  rw [←mul_sub,abs_mul,abs_of_nonneg S.kernel.penalty_pos.le]
  calc _ ≤ S.kernel.penalty*(2*G.chord (V b)) :=
             mul_le_mul_of_nonneg_left (price ..) S.kernel.penalty_pos.le
       _ = _ := by ring

private theorem noise (S : StepData c f) (β : ℝ) (Q V : Config G c) :
    Real.exp (-bill S β V)*S.noise β Q 1 ≤ S.noise β Q V ∧
      S.noise β Q V ≤ Real.exp (bill S β V)*S.noise β Q 1 := by
  let logRatio := -β*(noiseEnergy S Q V-noiseEnergy S Q 1)
  have bound : |logRatio| ≤ bill S β V := by
    dsimp only [logRatio,bill]
    rw [abs_mul,abs_neg]
    exact mul_le_mul_of_nonneg_left (energy S Q V) (abs_nonneg _)
  have eqn : S.noise β Q V=Real.exp logRatio*S.noise β Q 1 := by
    rw [noise_factor,noise_factor]
    unfold Gibbs.factor
    rw [mul_left_comm,←Real.exp_add]
    congr 2
    dsimp only [logRatio];ring
  rw [eqn]
  have pos : 0 ≤ S.noise β Q (1:Config G c) := (Push.BetaTransport.noise_pos S β Q 1).le
  exact ⟨mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (abs_le.mp bound).1) pos,
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (abs_le.mp bound).2) pos⟩

/-- The two terminal fields share all actual predictor weights, including
every common tag on the full lattice. The quiet normalization is external. -/
theorem original (S : StepData c f) (β : ℝ) (U : Config G f) (V : Config G c) :
    Real.exp (-bill S β V)*S.density β U 1 ≤ S.density β U V ∧
      S.density β U V ≤ Real.exp (bill S β V)*S.density β U 1 := by
  unfold StepData.density
  rw [Finset.mul_sum,Finset.mul_sum]
  constructor <;> apply Finset.sum_le_sum <;> intro a _
  · rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (noise S β (S.prediction U a) V).1 (S.likelihood_pos U a)
  · rw [mul_left_comm (Real.exp _)]
    exact mul_le_mul_of_nonneg_left (noise S β (S.prediction U a) V).2 (S.likelihood_pos U a)

end YM.Integration.WilsonOriginalDecoderSpring
end
