/- local Haar instances adapts the normalized Haar measure instances for UnitAddCircle from Mathlib/Analysis/Fourier/AddCircleMulti.lean for this project.
Authors: David Loeffler. Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache License 2.0. See NOTICE. -/

import YM.Integration.WilsonOriginalTorusPartialJets

/-! A single differentiation of the actual normalized torus integral,
including modes whose selected coordinate is zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFiledJetStep
open MeasureTheory UnitAddTorus Set
open scoped Interval
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T:=1)))

private theorem step (f g : UnitAddCircle → ℂ) (k : ℤ)
    (regular : Continuous (fun t : ℝ => g t))
    (diff : ∀ x ∈ [[(0:ℝ),1]], HasDerivAt (fun t : ℝ => f t) (g x) x) :
    (2*(Real.pi:ℂ)*Complex.I*(k:ℂ))*fourierCoeff f k = fourierCoeff g k := by
  have closed : f (↑(1:ℝ):UnitAddCircle) = f (↑(0:ℝ):UnitAddCircle) := by
    rw [AddCircle.coe_period,AddCircle.coe_zero]
  have cost : IntervalIntegrable (fun t : ℝ => g t) volume 0 1 := regular.intervalIntegrable ..
  rw [← WilsonOriginalCircleFourierJets.clocked f k,← WilsonOriginalCircleFourierJets.clocked g k]
  by_cases hk : k=0
  · subst k
    simp only [Int.cast_zero,mul_zero,zero_mul]
    rw [fourierCoeffOn_eq_integral]
    simp only [sub_zero,one_div,inv_one,one_smul,neg_zero,fourier_zero,one_smul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt diff cost,closed,sub_self]
  · have carry := fourierCoeffOn_of_hasDerivAt WilsonOriginalPeriodicSliceJets.width hk diff cost
    rw [closed,sub_self,mul_zero,zero_sub,Complex.ofReal_one,Complex.ofReal_zero,sub_zero,one_mul] at carry
    have nk : (k:ℂ) ≠ 0 := by exact_mod_cast hk
    have pp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [carry]
    field_simp [nk,pp,Complex.I_ne_zero]

theorem original {d : ℕ} (f g : C(UnitAddTorus (Fin (d+1)),ℂ)) (i : Fin (d+1))
    (diff : ∀ rest : Fin d → UnitAddCircle, ∀ x ∈ [[(0:ℝ),1]],
      HasDerivAt (fun t : ℝ => f (i.insertNth (t:UnitAddCircle) rest)) (g (i.insertNth (x:UnitAddCircle) rest)) x)
    (v : Fin (d+1) → ℤ) :
    (2*(Real.pi:ℂ)*Complex.I*(v i:ℂ))*mFourierCoeff f v = mFourierCoeff g v := by
  rw [WilsonOriginalDirectionalFourier.original f v i,WilsonOriginalDirectionalFourier.original g v i,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun rest => ?_)
  have cont : Continuous (fun t : ℝ => g (i.insertNth (t:UnitAddCircle) rest)) :=
    g.continuous.comp (Continuous.finInsertNth i (by fun_prop) continuous_const)
  have priced := step (fun x => f (i.insertNth x rest)) (fun x => g (i.insertNth x rest)) (v i) cont (diff rest)
  change _ = mFourier (fun j => -v (i.succAbove j)) rest *
    fourierCoeff (fun x => g (i.insertNth x rest)) (v i)
  rw [← priced]
  ring

end YM.Integration.WilsonOriginalFiledJetStep
