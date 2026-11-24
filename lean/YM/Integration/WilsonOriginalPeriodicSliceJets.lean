import Mathlib.Analysis.Fourier.AddCircle

/-! The actual integration by parts in one frequency direction on the
periodized box. Retain the other spatial coordinates as fixed parameters. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPeriodicSliceJets
open Real Complex MeasureTheory Set
open scoped Interval
theorem width : (0:ℝ)<1 := zero_lt_one

/-- The endpoints are identified at every derivative because the box
cutoff is supported in its interior. -/
theorem original (f : ℕ → ℝ → ℂ) (k : ℤ) (hk : k ≠ 0)
    (smooth : ∀ n x, x ∈ [[(0:ℝ),1]] → HasDerivAt (f n) (f (n+1) x) x)
    (same : ∀ n, f n 1 = f n 0) (n : ℕ) :
    (2*(Real.pi:ℂ)*Complex.I*(k:ℂ))^n * fourierCoeffOn width (f 0) k =
      fourierCoeffOn width (f n) k := by
  have integral (m : ℕ) : IntervalIntegrable (f (m+1)) volume 0 1 :=
    (show ContinuousOn (f (m+1)) [[(0:ℝ),1]] from
      fun x hx => (smooth (m+1) x hx).continuousAt.continuousWithinAt).intervalIntegrable
  have step (m : ℕ) : (2*(Real.pi:ℂ)*Complex.I*(k:ℂ))*fourierCoeffOn width (f m) k =
      fourierCoeffOn width (f (m+1)) k := by
    have carry := fourierCoeffOn_of_hasDerivAt width hk (smooth m) (integral m)
    rw [same,sub_self,mul_zero,zero_sub,Complex.ofReal_one,Complex.ofReal_zero,sub_zero,one_mul] at carry
    have nk : (k:ℂ) ≠ 0 := by exact_mod_cast hk
    have pp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [carry]
    field_simp [nk,pp,Complex.I_ne_zero]
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ',mul_assoc,ih,step]

end YM.Integration.WilsonOriginalPeriodicSliceJets

