import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

open Filter Set MeasureTheory
open scoped Topology Interval
namespace YM.Integration.WilsonPositionScaleLawMeasuredIntegral
variable {X Y V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V]

def line (y w : Y) (s : ℝ) : Y := y + s • (w-y)

theorem inverse (D : X → Y) (rev : Y → X) (y : Y) (A : X ≃L[ℝ] Y)
    (actual : HasFDerivAt D A.toContinuousLinearMap (rev y))
    (smooth : DifferentiableAt ℝ rev y) (solves : D ∘ rev =ᶠ[𝓝 y] id) :
    HasFDerivAt rev A.symm.toContinuousLinearMap y := by
  have chain := actual.comp y smooth.hasFDerivAt
  have same := (chain.congr_of_eventuallyEq solves.symm).unique (hasFDerivAt_id y)
  have undo : fderiv ℝ rev y=A.symm.toContinuousLinearMap := by
    ext v
    apply A.injective
    simpa using congrArg (fun T : Y →L[ℝ] Y => T v) same
  rw [← undo]
  exact smooth.hasFDerivAt

theorem exactContrast (D : X → Y) (H : X → V) (rev : Y → X)
    (J : X → X ≃L[ℝ] Y) (z : X) (w : Y) (h : V)
    (base : rev (D z)=z)
    (matrix : ∀ s ∈ uIcc (0:ℝ) 1, let y:=line (D z) w s
      HasFDerivAt D (J (rev y)).toContinuousLinearMap (rev y))
    (smooth : ∀ s ∈ uIcc (0:ℝ) 1, DifferentiableAt ℝ rev (line (D z) w s))
    (solves : ∀ s ∈ uIcc (0:ℝ) 1, D ∘ rev =ᶠ[𝓝 (line (D z) w s)] id)
    (target : ∀ s ∈ uIcc (0:ℝ) 1, DifferentiableAt ℝ H (rev (line (D z) w s)))
    (integrable : IntervalIntegrable (fun s=>let x:=rev (line (D z) w s)
      fderiv ℝ H x ((J x).symm (w-D z))) volume 0 1) :
    h-H z-(∫ s in (0:ℝ)..1, let x:=rev (line (D z) w s)
      fderiv ℝ H x ((J x).symm (w-D z)))=h-H (rev w) := by
  have path (s : ℝ) : HasDerivAt (line (D z) w) (w-D z) s := by
    change HasDerivAt (fun a:ℝ=>D z+a • (w-D z)) (w-D z) s
    simpa only [one_smul,zero_add] using!
      ((hasDerivAt_const s (D z)).add ((hasDerivAt_id' s).smul_const (w-D z)))
  have derivative (s : ℝ) (hs : s ∈ uIcc (0:ℝ) 1) :
      HasDerivAt (fun v=>H (rev (line (D z) w v)))
        (fderiv ℝ H (rev (line (D z) w s))
          ((J (rev (line (D z) w s))).symm (w-D z))) s := by
    exact (target s hs).hasFDerivAt.comp_hasDerivAt s
      ((inverse D rev _ _ (matrix s hs) (smooth s hs) (solves s hs)).comp_hasDerivAt s (path s))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt derivative integrable]
  simp only [line,one_smul,add_sub_cancel,zero_smul,add_zero,base]
  abel

end YM.Integration.WilsonPositionScaleLawMeasuredIntegral
