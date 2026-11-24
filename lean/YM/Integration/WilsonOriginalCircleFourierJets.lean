import YM.Integration.WilsonOriginalPeriodicSliceJets
import YM.Integration.WilsonOriginalDirectionalFourier

/-! The one-dimensional integration by parts has the same normalized
circle measure as the compact multidimensional physical integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCircleFourierJets
open MeasureTheory Set
open scoped Interval

theorem clocked (f : UnitAddCircle → ℂ) (k : ℤ) :
    fourierCoeffOn WilsonOriginalPeriodicSliceJets.width (fun x : ℝ => f x) k =
      fourierCoeff f k := by
  have lift : AddCircle.liftIoc (1:ℝ) 0 (fun x : ℝ => f x) = f := by
    funext a
    simp [AddCircle.liftIoc]
  have h := fourierCoeff_liftIoc_eq (T := (1:ℝ)) (a:=0) (fun x : ℝ => f x) k
  rw [lift] at h
  simpa only [zero_add] using h.symm

theorem original (f : ℕ → UnitAddCircle → ℂ) (k : ℤ) (hk : k ≠ 0)
    (smooth : ∀ n x, x ∈ [[(0:ℝ),1]] →
      HasDerivAt (fun t : ℝ => f n t) (f (n+1) x) x) (n : ℕ) :
    (2*(Real.pi:ℂ)*Complex.I*(k:ℂ))^n * fourierCoeff (f 0) k =
      fourierCoeff (f n) k := by
  have closed (j : ℕ) : f j (↑(1:ℝ):UnitAddCircle) = f j (↑(0:ℝ):UnitAddCircle) := by
    rw [AddCircle.coe_period,AddCircle.coe_zero]
  simpa only [clocked] using WilsonOriginalPeriodicSliceJets.original
    (fun j (x:ℝ) => f j x) k hk smooth closed n

end YM.Integration.WilsonOriginalCircleFourierJets

