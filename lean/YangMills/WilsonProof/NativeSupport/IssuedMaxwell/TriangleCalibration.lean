import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.TriangleBulk
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.TriangleColors
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedMaxwell.TriangleCalibration
open YM YM.XSpace YM.XSpace.Chiral YangMills.MSbar YangMills.MSbar.Position MeasureTheory
open TriangleLines TriangleBulk
variable (g:YangMills.GaugeGroup)

theorem graph (c:Shade.Cut)(x:YM.Points 3):bareTriangle (Reference.issued g) c x =
    Rose.numeric g.core c (x 0) (x 1) (x 2):=by
  change 6*Cubic.colorNorm (Reference.issued g)*∑ i:Fin 3,∑ j:Fin 3,∑ k:Fin 3,
    Cubic.orientation i j k*(∑ m:Fin 3,∑ n:Fin 3,
      double j m (x 0-x 1)*double k n (x 0-x 2)*vertex c i m n (x 0) (x 1) (x 2))=_
  simp only [TriangleColors.original,TriangleAxes.orientation,TriangleLines.original,TriangleBulk.original,
    Rose.numeric]
theorem price (P:PositionPrescription (Reference.issued g)):
    Rose.cT P.triangle.cut g.core (NegativePupil.real P.triangle.profile)=P.triangle.cT:=by
  unfold Rose.cT Position.Triangle.cT
  apply integral_congr_ae
  filter_upwards with x
  rw [graph]
  rfl
theorem original (P:PositionPrescription (Reference.issued g))(H:Admissible P):
    Rose.cT P.triangle.cut g.core (NegativePupil.real P.triangle.profile)<0:=by
  rw [price];exact H.calibration.negative
end IssuedMaxwell.TriangleCalibration
end
