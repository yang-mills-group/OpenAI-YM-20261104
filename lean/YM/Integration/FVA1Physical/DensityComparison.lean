import YM.Integration.FVA1Physical.ActualPush

/-! Comparing an exact physical density with a sequence of unnormalized forecasts. -/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical

open MeasureTheory RG Lattice Wilson
open scoped BigOperators

variable {G : Gauge} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Transporting an already normalized density cancels its fine vacuum and divides by
the actual coarse vacuum. This identity holds at every field of every selected slice. -/
theorem conditionalPush_normalized (A : History G) (h : A.Selected) (N p m : ℕ)
    (hm : m < N) (D : Config G (A.S.side (m + 1) p) → E) (V : Config G (A.S.side m p)) :
    conditionalPush A N p m (fun U => ((A.rep N p (m + 1)).eval U)⁻¹ • D U) V =
      ((A.rep N p m).eval V)⁻¹ • (A.levels.clock.op m p).push (A.β N p (m + 1)) D V := by
  have cancel : (fun U => (A.rep N p (m + 1)).eval U •
      (((A.rep N p (m + 1)).eval U)⁻¹ • D U)) = D := by
    funext U
    rw [smul_smul, mul_inv_cancel₀ (SectorNext.Vacuum.strictly A h N p (m + 1) hm U).ne',
      one_smul]
  simp only [conditionalPush, cancel]

/-- For two raw densities, only the forecast's local defect and the initial discrepancy
enter the accumulated normalized error. The exact density supplies its literal blocking law.
The forecast may be fixed before the exact density is compared with it. -/
theorem density_forecast_error (A : History G) (h : A.Selected) (N p : ℕ)
    (D F : (m : ℕ) → Config G (A.S.side m p) → E) (b : ℝ) (cost : ℕ → ℝ)
    (raw : ∀ k < N, D k = (A.levels.clock.op k p).push (A.β N p (k + 1)) (D (k + 1)))
    (intD : ∀ k < N, Integrable (D (k + 1)) (prior G (A.S.side (k + 1) p)))
    (intF : ∀ k < N, Integrable (F (k + 1)) (prior G (A.S.side (k + 1) p)))
    (top : ∀ U, ‖((A.rep N p N).eval U)⁻¹ • (D N U - F N U)‖ ≤ b)
    (localCost : ∀ k < N, ∀ V, ‖((A.rep N p k).eval V)⁻¹ •
      ((A.levels.clock.op k p).push (A.β N p (k + 1)) (F (k + 1)) V - F k V)‖ ≤ cost k)
    (m : ℕ) (hm : m ≤ N) (V : Config G (A.S.side m p)) :
    ‖((A.rep N p m).eval V)⁻¹ • (D m V - F m V)‖ ≤ b + ∑ j ∈ Finset.Ico m N, cost j := by
  apply accumulated_physical_error A h N p (fun k U => ((A.rep N p k).eval U)⁻¹ •
    (D k U - F k U)) b cost top _ m hm V
  intro k hk W
  let S := A.levels.clock.op k p
  let β := A.β N p (k + 1)
  have hker : S.IsKernel β G := A.levels.transition_mass k p β
  have hsub : S.push β (fun U => D (k + 1) U - F (k + 1) U) W =
      S.push β (D (k + 1)) W - S.push β (F (k + 1)) W := by
    simp only [StepData.push, smul_sub]
    exact integral_sub (StepData.push_slice hker W _ (intD k hk))
      (StepData.push_slice hker W _ (intF k hk))
  rw [conditionalPush_normalized A h N p k hk, hsub, ← smul_sub]
  have diff : D k W - F k W - (S.push β (D (k + 1)) W - S.push β (F (k + 1)) W) =
      S.push β (F (k + 1)) W - F k W := by
    rw [congrFun (raw k hk) W]
    dsimp only [S, β]
    abel
  rw [diff]
  exact localCost k hk W

end YM.Integration.FVA1Physical
