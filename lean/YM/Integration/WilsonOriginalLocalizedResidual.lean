/- local Haar instances adapts the normalized Haar measure instances for UnitAddCircle from Mathlib/Analysis/Fourier/AddCircleMulti.lean for this project.
Authors: David Loeffler. Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache License 2.0. See NOTICE. -/

import YM.Integration.WilsonOriginalMixedFourierRead
import YM.Integration.WilsonOriginalFourierReadback

/-! A single normalized Fourier evaluation of the physical field minus
the complete finite, same-temperature expansion. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalLocalizedResidual
open MeasureTheory UnitAddTorus
open scoped Topology BigOperators
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T:=1)))

private theorem integrable {d : ℕ} (v : Fin d → ℤ) (f : C(UnitAddTorus (Fin d),ℂ)) :
    Integrable (fun x => mFourier (-v) x*f x) := by
  exact ((mFourier (-v)).continuous.mul f.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def read {d : ℕ} (v : Fin d → ℤ) : C(UnitAddTorus (Fin d),ℂ) →ₗ[ℂ] ℂ where
  toFun f := mFourierCoeff f v
  map_add' f g := by
    change (∫ x, mFourier (-v) x*(f x+g x)) = _+_
    simp only [mul_add]
    exact integral_add (integrable v f) (integrable v g)
  map_smul' b f := by
    change (∫ x, mFourier (-v) x*(b*f x)) = b * (∫ x, mFourier (-v) x*f x)
    rw [← integral_const_mul]
    apply integral_congr_ae (Filter.Eventually.of_forall fun _ => by ring)

def field {d : ℕ} (t : ℝ) (p : ℕ) (f : C(UnitAddTorus (Fin d),ℂ))
    (a : ℕ → C(UnitAddTorus (Fin d),ℂ)) :=
  f-∑ k : Fin (p+1), (t:ℂ)^k.val • a k.val

theorem original {d : ℕ} (t : ℝ) (p : ℕ) (f : C(UnitAddTorus (Fin d),ℂ))
    (a : ℕ → C(UnitAddTorus (Fin d),ℂ)) (v : Fin d → ℤ) :
    mFourierCoeff (field t p f a) v = WilsonOriginalSignedTailSum.remainder t p
      (fun z => mFourierCoeff f z) (fun k z => mFourierCoeff (a k) z) v := by
  change read v (f-∑ k : Fin (p+1), (t:ℂ)^k.val • a k.val) = _
  simp only [map_sub,map_sum,map_smul,smul_eq_mul]
  rfl
end YM.Integration.WilsonOriginalLocalizedResidual
