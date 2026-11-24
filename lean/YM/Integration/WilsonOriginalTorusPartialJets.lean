/- local Haar instances adapts the normalized Haar measure instances for UnitAddCircle from Mathlib/Analysis/Fourier/AddCircleMulti.lean for this project.
Authors: David Loeffler. Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache License 2.0. See NOTICE. -/

import YM.Integration.WilsonOriginalCircleFourierJets

/-! The complete deposited multidimensional field may be differentiated
in the one selected spatial direction before bounding its Fourier modes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTorusPartialJets
open MeasureTheory UnitAddTorus Set
open scoped Interval
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T:=1)))

theorem original {d : ℕ} (f : ℕ → C(UnitAddTorus (Fin (d+1)),ℂ))
    (v : Fin (d+1) → ℤ) (i : Fin (d+1)) (hk : v i ≠ 0)
    (smooth : ∀ rest : Fin d → UnitAddCircle, ∀ n x, x ∈ [[(0:ℝ),1]] →
      HasDerivAt (fun t : ℝ => f n (i.insertNth (t:UnitAddCircle) rest))
        (f (n+1) (i.insertNth (x:UnitAddCircle) rest)) x) (n : ℕ) :
    (2*(Real.pi:ℂ)*Complex.I*(v i:ℂ))^n*mFourierCoeff (f 0) v = mFourierCoeff (f n) v := by
  rw [WilsonOriginalDirectionalFourier.original (f 0) v i,WilsonOriginalDirectionalFourier.original (f n) v i,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun rest => ?_)
  have eq := WilsonOriginalCircleFourierJets.original (fun m x => f m (i.insertNth x rest)) (v i)
    hk (smooth rest) n
  change (2*(Real.pi:ℂ)*Complex.I*(v i:ℂ))^n *
      (mFourier (fun j => -v (i.succAbove j)) rest *
        fourierCoeff (fun x => f 0 (i.insertNth x rest)) (v i)) =
    mFourier (fun j => -v (i.succAbove j)) rest *
      fourierCoeff (fun x => f n (i.insertNth x rest)) (v i)
  rw [← eq]
  ring

end YM.Integration.WilsonOriginalTorusPartialJets

