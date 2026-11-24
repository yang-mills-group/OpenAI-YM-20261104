/- local Haar instances adapts the normalized Haar measure instances for UnitAddCircle from Mathlib/Analysis/Fourier/AddCircleMulti.lean for this project.
Authors: David Loeffler. Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache License 2.0. See NOTICE. -/

import Mathlib.Analysis.Real.Pi.Bounds
import YM.Integration.WilsonOriginalTorusPartialJets
import YM.Integration.WilsonOriginalFourierLattice

/-! Price the actual integral in its chosen largest frequency direction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTorusDerivativePrice
open MeasureTheory UnitAddTorus Set
open scoped Interval
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T:=1)))

theorem value {d : ℕ} (f : C(UnitAddTorus (Fin d),ℂ)) (v : Fin d → ℤ)
    (C : ℝ) (income : ∀ x, ‖f x‖ ≤ C) : ‖mFourierCoeff f v‖ ≤ C := by
  change ‖∫ x,mFourier (-v) x*f x‖ ≤ C
  have signed (x) : ‖mFourier (-v) x*f x‖ ≤ C := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg (f x))
      (((mFourier (-v)).norm_coe_le_norm x).trans_eq mFourier_norm)).trans (income x)
  simpa using norm_integral_le_of_norm_le_const (μ:=volume) (ae_of_all _ signed)

theorem original {d : ℕ} (f : ℕ → C(UnitAddTorus (Fin (d+1)),ℂ)) (v : Fin (d+1) → ℤ)
    (i : Fin (d+1)) (highest : (v i).natAbs = WilsonOriginalFourierLattice.height v)
    (smooth : ∀ rest : Fin d → UnitAddCircle, ∀ n x, x ∈ [[(0:ℝ),1]] →
      HasDerivAt (fun t : ℝ => f n (i.insertNth (t:UnitAddCircle) rest))
        (f (n+1) (i.insertNth (x:UnitAddCircle) rest)) x)
    (n : ℕ) (bound : ℝ) (positive : 0 ≤ bound) (income : ∀ x, ‖f n x‖ ≤ bound) :
    ‖mFourierCoeff (f 0) v‖ * (WilsonOriginalFourierLattice.height v:ℝ)^n ≤ bound := by
  by_cases h : v i = 0
  · cases n with
    | zero => simpa using (value (f 0) v bound income)
    | succ n => simp only [← highest,h,Int.natAbs_zero,Nat.cast_zero,zero_pow (Nat.succ_ne_zero n),mul_zero];exact positive
  have mark := WilsonOriginalTorusPartialJets.original f v i h smooth n
  have size : ((v i).natAbs:ℝ) ≤ ‖2*(Real.pi:ℂ)*Complex.I*(v i:ℂ)‖ := by
    have a : ‖((v i:ℤ):ℂ)‖ = ((v i).natAbs:ℝ) := by simp
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
      Complex.norm_I,mul_one,a]
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith [Real.pi_gt_three])
  calc
    _ ≤ ‖mFourierCoeff (f 0) v‖ * ‖2*(Real.pi:ℂ)*Complex.I*(v i:ℂ)‖^n := by
      rw [← highest]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) size _) (norm_nonneg _)
    _ = ‖mFourierCoeff (f n) v‖ := by
      symm
      calc
        _ = ‖(2*(Real.pi:ℂ)*Complex.I*(v i:ℂ))^n*mFourierCoeff (f 0) v‖ := congrArg Norm.norm mark.symm
        _ = _ := by rw [norm_mul,norm_pow,mul_comm]
    _ ≤ _ := value _ _ _ income

end YM.Integration.WilsonOriginalTorusDerivativePrice

