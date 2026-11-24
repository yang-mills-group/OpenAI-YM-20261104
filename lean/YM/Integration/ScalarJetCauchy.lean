import YM.Integration.NormalizedJetCauchy

/-! Public scalar-direction consequences of the unchanged joint Cauchy formula. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ScalarJetCauchy

open Finset Function
open YM.Comparison.RG02.Assembly
open YM.Integration.NormalizedJetCauchy
open scoped BigOperators ContDiff Topology

/-- Exact normalized Cauchy formula in the single scalar direction. -/
theorem scalar_product_jet (h f : ℝ → ℝ)
    (hh : ContDiffAt ℝ ω h 0) (hf : ContDiffAt ℝ ω f 0) (n : ℕ) :
    jet (fun t => h t * f t) n 1 =
      ∑ c ∈ range (n + 1), jet h c 1 * jet f (n - c) 1 := by
  let P : ℝ × ℝ → ℝ := fun z => h z.1 * f z.2
  let L : ℝ →L[ℝ] ℝ × ℝ := ContinuousLinearMap.toSpanSingleton ℝ (1, 1)
  have hP : ContDiffAt ℝ ω P 0 :=
    (hh.comp (0 : ℝ × ℝ) contDiffAt_fst).mul
      (hf.comp (0 : ℝ × ℝ) contDiffAt_snd)
  have he : jet (fun t => h t * f t) n 1 = jet P n (1, 1) := by
    simpa [P, L, Function.comp_def] using
      jet_continuous_right L (hP.of_le le_top) (1 : ℝ)
  exact he.trans (product_jet h f hh hf n 1)

/-- No centering is required for the scalar modifier bound. -/
theorem scalar_product_bound (h f : ℝ → ℝ)
    (hh : ContDiffAt ℝ ω h 0) (hf : ContDiffAt ℝ ω f 0)
    (n : ℕ) (H F : ℝ) (hH : 0 ≤ H) (_hF : 0 ≤ F)
    (hs : ∀ c ≤ n, ‖jet h c 1‖ ≤ H)
    (hb : ∀ k ≤ n, ‖jet f k 1‖ ≤ F) :
    ‖jet (fun t => h t * f t) n 1‖ ≤ (n + 1 : ℝ) * H * F := by
  rw [scalar_product_jet h f hh hf n]
  calc
    _ ≤ ∑ c ∈ range (n + 1), ‖jet h c 1 * jet f (n - c) 1‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ range (n + 1), H * F := by
      apply Finset.sum_le_sum
      intro c hc
      rw [norm_mul]
      exact mul_le_mul (hs c (Nat.le_of_lt_succ (mem_range.mp hc)))
        (hb (n - c) (Nat.sub_le _ _)) (norm_nonneg _) hH
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      ring

end YM.Integration.ScalarJetCauchy
end
