import YM.Integration.WilsonLocalKernelPriceExpansion

/-! Exponential concentration of the sum of the actual selected Wilson link prices. -/
noncomputable section
namespace YM.Integration.WilsonLocalKernelConcentration
open YM RG Lattice Wilson MeasureTheory Set WilsonKernelCoupling WilsonLocalKernelLaplace
open scoped BigOperators
variable {c f : Side} (S : StepData c f) {G : Gauge}

def score (A : Finset (Edge (Site c))) (Q V : Config G c) : ℝ :=
  ∑ i : A, S.kernel.penalty * G.price (V i.val * (Q i.val)⁻¹)

theorem score_continuous (A : Finset (Edge (Site c))) (Q : Config G c) :
    Continuous (score S A Q) := by
  unfold score
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (G.continuous_price.comp ((continuous_apply i.val).mul continuous_const))

theorem exponential (A : Finset (Edge (Site c))) (b h : ℝ) (Q V : Config G c) :
    tilt S A b (fun _ => b-h) Q (readLinks A V) = Real.exp (h * score S A Q V) := by
  simp only [tilt, StepData.penaltyWeight, readLinks, score, ← Real.exp_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem moment (A : Finset (Edge (Site c))) (b h : ℝ) (Q : Config G c) :
    (∫ V, S.noise b Q V * Real.exp (h * score S A Q V) ∂prior G c) =
      (S.penaltyZ (b-h) G / S.penaltyZ b G)^A.card := by
  have y := WilsonLocalKernelLaplace.measured S A b (fun _ => b-h) Q
  simpa only [exponential, Finset.prod_const, Finset.card_univ, Fintype.card_coe] using y

theorem tail (A : Finset (Edge (Site c))) (b u : ℝ) {h : ℝ} (hh : 0 ≤ h) (Q : Config G c) :
    (∫ V in {V | u ≤ score S A Q V}, S.noise b Q V ∂prior G c) ≤
      Real.exp (-h*u) * (S.penaltyZ (b-h) G / S.penaltyZ b G)^A.card := by
  let T := {V | u ≤ score S A Q V}
  have hs : MeasurableSet T := measurableSet_le measurable_const (score_continuous S A Q).measurable
  letI : IsFiniteMeasureOnCompacts (prior G c) :=
    inferInstanceAs (IsFiniteMeasureOnCompacts (Measure.pi fun _ : Edge (Site c) => G.probHaar))
  have hc : Continuous (fun V => S.noise b Q V * Real.exp (h*score S A Q V)) :=
    ((S.noise_cont b).comp (continuous_const.prodMk continuous_id)).mul
      (Real.continuous_exp.comp (continuous_const.mul (score_continuous S A Q)))
  have hi := hc.integrable_of_hasCompactSupport (μ:=prior G c) (HasCompactSupport.of_compactSpace _)
  have hn (V : Config G c) : 0 ≤ S.noise b Q V :=
    Finset.prod_nonneg fun i _ => mul_nonneg (inv_pos.mpr (S.penaltyZ_pos b)).le (Real.exp_pos _).le
  rw [← integral_indicator hs, ← moment S A b h Q, ← integral_const_mul]
  apply integral_mono ((S.noise_integrable b Q).indicator hs) (hi.const_mul _)
  intro V
  change T.indicator (S.noise b Q) V ≤ Real.exp (-h*u) * (S.noise b Q V * Real.exp (h * score S A Q V))
  by_cases hx : V ∈ T
  · rw [Set.indicator_of_mem hx]
    have h1 : 1 ≤ Real.exp (-h*u) * Real.exp (h*score S A Q V) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      have ht : 0 ≤ h*(score S A Q V-u) := mul_nonneg hh (sub_nonneg.mpr hx)
      linarith only [ht]
    calc
      _ ≤ S.noise b Q V * (Real.exp (-h*u)*Real.exp (h*score S A Q V)) :=
        le_mul_of_one_le_right (hn V) h1
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hx]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (hn V) (Real.exp_pos _).le)

theorem physical (hB : S.patch.Branches S.kernel G) (A : Finset (Edge (Site c)))
    (b u : ℝ) {h : ℝ} (hh : 0 ≤ h) (U : Config G f) :
    (∑ z, S.likelihood U z * ∫ V in {V | u ≤ score S A (S.prediction U z) V},
      S.noise b (S.prediction U z) V ∂prior G c) ≤
      Real.exp (-h*u) * (S.penaltyZ (b-h) G / S.penaltyZ b G)^A.card := by
  calc
    _ ≤ ∑ z, S.likelihood U z * (Real.exp (-h*u) * (S.penaltyZ (b-h) G / S.penaltyZ b G)^A.card) :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (tail S A b u hh _) (S.likelihood_pos U z)
    _ = _ := by rw [← Finset.sum_mul, S.chosen hB, one_mul]

end YM.Integration.WilsonLocalKernelConcentration
