import YM.Integration.WilsonThermometerPositionFilmAngularGround
import YM.Integration.WilsonMarkedRelativeForestChart

/-! The original lower angular tangent on its actual translated finite Gaussian. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmAxisSalary
open Function Finset Matrix Lattice Wilson Exterior Precision RG Next.Free UVExtension.Free Tree Work.F03
open Primitives.TwoWave Primitives.TwoWave.RealSlice PhysicalNext.Repeat.Legato Comparison.RG02
open Next.SectorChange
open WilsonThermometerPositionFilmCubicGeometry WilsonMarkedRelativeForestChart
open scoped Classical BigOperators ContDiff
variable {G:Gauge} {c f:Side} {S:StepData c f}

def fee (G:Gauge):ℝ:=1+‖iteratedFDeriv ℝ 1 (localLog G) 0‖

theorem direction_price (F:Forest S.ratio)(u:Bulk.SliceDir S F G):
    1+‖direction F u‖≤fee G*(1+‖u‖):=by
  have bound:=WilsonMarkedRelativeForestChart.full F 1 (fun _=>u)
  simp only [iteratedFDeriv_one_apply,Fin.prod_univ_one] at bound
  unfold direction fee
  nlinarith [norm_nonneg u,norm_nonneg (iteratedFDeriv ℝ 1 (localLog G) 0)]

def colors (G:Gauge):(G.ColorIndex→ℝ)≃L[ℝ]G.Color:=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _:G.ColorIndex=>ℝ)).symm

def noise (G:Gauge):ℝ:=‖(colors G).toContinuousLinearMap‖

private theorem physical_noise (F:Forest S.ratio)(z:(F.Free×G.ColorIndex)→ℝ):
    ‖(tape z:AxisChart G F)‖≤noise G*‖z‖:=by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  intro e
  change ‖(colors G) (fun k=>z (e,k))‖≤_
  apply ((colors G).toContinuousLinearMap.le_opNorm _).trans
  exact mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg (norm_nonneg z)).2
    (fun k=>norm_le_pi_norm z (e,k))) (norm_nonneg _)

variable {clip:Clip}{P:PathData G}{O:ChartRatio G}(K:Bulk.Kernel S clip P O)(F:Forest S.ratio)
    (x:fieldDir G c 1)
def room : ℝ:=1+‖x‖+‖fderiv ℝ (K.b F) 0 x‖+noise G

theorem original (z:(F.Free×G.ColorIndex)→ℝ):
    1+‖direction F (Bulk.translated K F x z).2‖≤fee G*room K F x*(1+‖z‖):=by
  apply (direction_price F _).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by unfold fee;positivity)
  rw [Bulk.footing,Prod.norm_def]
  apply add_le_of_le_sub_left
  apply max_le
  · unfold room noise; nlinarith [norm_nonneg x,norm_nonneg z,norm_nonneg (fderiv ℝ (K.b F) 0 x),
        norm_nonneg (colors G).toContinuousLinearMap,
        mul_nonneg (norm_nonneg x) (norm_nonneg z),
        mul_nonneg (norm_nonneg (fderiv ℝ (K.b F) 0 x)) (norm_nonneg z),
        mul_nonneg (norm_nonneg (colors G).toContinuousLinearMap) (norm_nonneg z)]
  · apply (norm_add_le ..).trans
    apply (add_le_add (le_refl _) (physical_noise F z)).trans
    unfold room noise; nlinarith [norm_nonneg x,norm_nonneg z,norm_nonneg (fderiv ℝ (K.b F) 0 x),
        norm_nonneg (colors G).toContinuousLinearMap,
        mul_nonneg (norm_nonneg x) (norm_nonneg z),
        mul_nonneg (norm_nonneg (fderiv ℝ (K.b F) 0 x)) (norm_nonneg z)]

end YM.Integration.WilsonThermometerPositionFilmAxisSalary
end
