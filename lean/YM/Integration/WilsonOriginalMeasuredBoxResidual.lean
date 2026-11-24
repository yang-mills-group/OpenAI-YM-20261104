import YM.Integration.WilsonOriginalCompactTorusChart
import YM.Integration.WilsonOriginalLocalizedResidual

/-! Payment for the entire measured compact difference on one genuine
modulated test, including all the lower coefficients and the unit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMeasuredBoxResidual
open Set MeasureTheory UnitAddTorus
open WilsonOriginalFourierBoxIntegral (localize test)
open scoped BigOperators

def chart {d : ℕ} (a l h : Fin d → ℝ) (f : (Fin d → ℝ) → ℂ)
    (left : ∀ i, a i ≤ l i) (right : ∀ i, h i ≤ a i+1)
    (sf : ContinuousOn f {x | ∀ i, x i ∈ Icc (a i) (a i+1)}) :
    C(UnitAddTorus (Fin d),ℂ) :=
  ⟨localize a l h f,WilsonOriginalCompactTorusChart.original a l h f left right sf⟩

theorem original {d : ℕ} (a l h : Fin d → ℝ) (v : Fin d → ℤ)
    (f : (Fin d → ℝ) → ℂ) (coeff : ℕ → (Fin d → ℝ) → ℂ)
    (u : ℝ) (p : ℕ) (left : ∀ i, a i ≤ l i) (right : ∀ i, h i ≤ a i+1)
    (sf : ContinuousOn f {x | ∀ i, x i ∈ Icc (a i) (a i+1)})
    (sc : ∀ k, ContinuousOn (coeff k) {x | ∀ i, x i ∈ Icc (a i) (a i+1)}) :
    mFourierCoeff (WilsonOriginalLocalizedResidual.field u p (chart a l h f left right sf)
      (fun k => chart a l h (coeff k) left right (sc k))) v =
      (∫ x, test l h v x*f x) - ∑ k : Fin (p+1),
        (u:ℂ)^k.val*(∫ x, test l h v x*coeff k.val x) := by
  rw [WilsonOriginalLocalizedResidual.original]
  simp only [WilsonOriginalSignedTailSum.remainder,chart,ContinuousMap.coe_mk,
    WilsonOriginalFourierBoxIntegral.original a l h v _ left right]

end YM.Integration.WilsonOriginalMeasuredBoxResidual
