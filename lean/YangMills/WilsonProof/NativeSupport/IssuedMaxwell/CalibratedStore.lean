import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.CutBudget
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedMaxwell.CalibratedStore
open YM YM.XSpace YangMills.MSbar MeasureTheory
variable {g:YangMills.GaugeGroup} (simple:g.core.Simple)
variable (P:PositionPrescription (Reference.issued g))(H:Admissible P)

def issued:Rose.Pick (PositionStore.original P H) where
  cut:=P.triangle.cut
  grants:=PositionStore.granted P H
  manages:=CutBudget.original g.core 6 P.triangle.cut simple (by decide)
  image:=NegativePupil.real P.triangle.profile
  spins:=(NegativePupil.original P H).1
  segment:=(NegativePupil.original P H).2.1
  fresh:=TriangleCalibration.original g P H

theorem original :
    (issued simple P H).cut=P.triangle.cut ∧
    (∀x,((issued simple P H).image x:ℂ)=P.triangle.profile x) ∧
    Rose.cT (issued simple P H).cut g.core (issued simple P H).image=P.triangle.cT ∧
    ∀d (Q:Normalize.Prediction g.core d),(((PositionStore.original P H).measure d).D Q).val=
      (P.screen d).read (Reports.printed Q):=
  ⟨rfl,(NegativePupil.original P H).2.2,TriangleCalibration.price g P,PositionStore.reported P H⟩
end IssuedMaxwell.CalibratedStore
end
