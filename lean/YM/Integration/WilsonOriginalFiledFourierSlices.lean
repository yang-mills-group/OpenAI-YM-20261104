/- local Haar instances adapts the normalized Haar measure instances for UnitAddCircle from Mathlib/Analysis/Fourier/AddCircleMulti.lean for this project.
Authors: David Loeffler. Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache License 2.0. See NOTICE. -/

import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.Prod

/-! Split the authentic torus integral at its chosen frequency direction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFiledFourierSlices
open MeasureTheory UnitAddTorus
open scoped BigOperators
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T:=1)))

theorem original {d : ℕ} (f : C(UnitAddTorus (Fin (d+1)),ℂ))
    (v : Fin (d+1) → ℤ) (i : Fin (d+1)) :
    let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => UnitAddCircle) i
    mFourierCoeff f v = ∫ rest : Fin d → UnitAddCircle, ∫ x : UnitAddCircle,
      mFourier (-v) (split.symm (x,rest))*f (split.symm (x,rest)) := by
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => UnitAddCircle) i
  let integrand := fun x : UnitAddTorus (Fin (d+1)) => mFourier (-v) x * f x
  have price : Integrable integrand := ((mFourier (-v)).continuous.mul f.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have layout := volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => UnitAddCircle) i
  have slice : Integrable (integrand ∘ split.symm) := (layout.symm.integrable_comp_emb
    split.symm.measurableEmbedding).mpr price
  change (∫ x,integrand x) = _
  rw [← layout.symm.integral_comp' integrand]
  exact integral_prod_symm _ slice

end YM.Integration.WilsonOriginalFiledFourierSlices

