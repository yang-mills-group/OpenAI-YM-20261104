/- local Haar instances adapts the normalized Haar measure instances for UnitAddCircle from Mathlib/Analysis/Fourier/AddCircleMulti.lean for this project.
Authors: David Loeffler. Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache License 2.0. See NOTICE. -/

import YM.Integration.WilsonOriginalOneCircleExpense
import YM.Integration.WilsonOriginalDirectionalFourier
import YM.Integration.WilsonOriginalTorusDerivativePrice

/-! The full torus coefficient is priced by the genuine directional
derivative on the coordinate of highest frequency. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTorusAxisExpense
open MeasureTheory Set UnitAddTorus
open WilsonOriginalFourierLattice (height)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T:=1)))

theorem original {d : ℕ} (F : C(UnitAddTorus (Fin (d+1)),ℂ))
    (v : Fin (d+1) → ℤ) (i : Fin (d+1)) (high : (v i).natAbs = height v)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (smooth : ∀ (rest : Fin d → UnitAddCircle) j t, t ∈ Icc (0:ℝ) 1 →
      DifferentiableAt ℝ (iteratedDeriv j (fun s : ℝ => F (i.insertNth (s:UnitAddCircle) rest))) t)
    (price : ∀ (rest : Fin d → UnitAddCircle) t, t ∈ Icc (0:ℝ) 1 →
      ‖iteratedDeriv n (fun s : ℝ => F (i.insertNth (s:UnitAddCircle) rest)) t‖ ≤ C) :
    ‖mFourierCoeff F v‖*(height v:ℝ)^n ≤ C := by
  by_cases zero : v i = 0
  · cases n with
    | succ j => simp [← high,zero,hC]
    | zero =>
      simp only [pow_zero,mul_one]
      apply WilsonOriginalTorusDerivativePrice.value
      intro z
      let t := AddCircle.equivIoc (1:ℝ) 0 (z i)
      have cover : ((t.val:ℝ):UnitAddCircle) = z i := AddCircle.coe_equivIoc
      have inc : t.val ∈ Icc (0:ℝ) 1 := ⟨t.property.1.le,by simpa using t.property.2⟩
      simpa only [iteratedDeriv_zero,cover,Fin.insertNth_self_removeNth] using price (i.removeNth z) t.val inc
  let k := (2*(Real.pi:ℂ)*Complex.I*(v i:ℂ))
  have val : ((v i).natAbs:ℝ) ≤ ‖k‖ := by
    have a : ‖((v i:ℤ):ℂ)‖ = ((v i).natAbs:ℝ) := by simp
    simp only [k,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
      Complex.norm_I,mul_one,a]
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith [Real.pi_gt_three])
  let G (rest : Fin d → UnitAddCircle) := mFourier (fun j => -v (i.succAbove j)) rest*
      fourierCoeff (fun z : UnitAddCircle => F (i.insertNth z rest)) (v i)
  have paid (rest : Fin d → UnitAddCircle) : ‖k^n*G rest‖ ≤ C := by
    have own := WilsonOriginalOneCircleExpense.original (fun z : UnitAddCircle => F (i.insertNth z rest))
      (v i) zero n C (smooth rest) (price rest)
    dsimp only [G]
    rw [mul_left_comm,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (((mFourier _).norm_coe_le_norm _).trans_eq mFourier_norm)).trans own
  calc
    _ ≤ ‖mFourierCoeff F v‖*‖k‖^n := by
      rw [← high];gcongr
    _ = ‖k^n*mFourierCoeff F v‖ := by conv_rhs => rw [norm_mul,norm_pow,mul_comm]
    _ = ‖∫ rest, k^n*G rest‖ := by rw [WilsonOriginalDirectionalFourier.original F v i,integral_const_mul]
    _ ≤ C := by simpa using norm_integral_le_of_norm_le_const (μ:=volume) (ae_of_all _ paid)

end YM.Integration.WilsonOriginalTorusAxisExpense
