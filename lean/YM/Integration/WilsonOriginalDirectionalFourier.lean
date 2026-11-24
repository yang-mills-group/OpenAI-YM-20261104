/- local Haar instances adapts the normalized Haar measure instances for UnitAddCircle from Mathlib/Analysis/Fourier/AddCircleMulti.lean for this project.
Authors: David Loeffler. Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache License 2.0. See NOTICE. -/

import YM.Integration.WilsonOriginalFiledFourierSlices

/-! One-dimensional Haar integration on the actual varied coordinate. The
remaining character and the full original field stay on the same torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalDirectionalFourier
open MeasureTheory UnitAddTorus
open scoped BigOperators
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T:=1)))

theorem original {d : ℕ} (f : C(UnitAddTorus (Fin (d+1)),ℂ))
    (v : Fin (d+1) → ℤ) (i : Fin (d+1)) :
    mFourierCoeff f v = ∫ rest : Fin d → UnitAddCircle,
      mFourier (fun j => -v (i.succAbove j)) rest *
        fourierCoeff (fun x : UnitAddCircle => f (i.insertNth x rest)) (v i) := by
  rw [WilsonOriginalFiledFourierSlices.original f v i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun rest => ?_)
  change (∫ x : UnitAddCircle,
      mFourier (-v) (i.insertNth x rest) * f (i.insertNth x rest)) =
    mFourier (fun j => -v (i.succAbove j)) rest *
      ∫ x : UnitAddCircle, fourier (-v i) x * f (i.insertNth x rest)
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change mFourier (-v) (i.insertNth x rest)*f (i.insertNth x rest) =
    mFourier (fun j => -v (i.succAbove j)) rest *
      (fourier (-(v i)) x * f (i.insertNth x rest))
  simp only [mFourier,ContinuousMap.coe_mk,Pi.neg_apply]
  rw [i.prod_univ_succAbove]
  simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
  ring

end YM.Integration.WilsonOriginalDirectionalFourier

