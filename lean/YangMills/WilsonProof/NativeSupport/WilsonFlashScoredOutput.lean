import YangMills.WilsonProof.NativeSupport.OPEMatching.PhysicalCoefficients
import YangMills.WilsonProof.NativeSupport.CorrelationMatching.Construction.Estimates
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedOrdinaryPacket
import YM.Integration.WilsonGraphPublishedReturnLaws

set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonFlashScoredOutput
open YangMills YangMills.Matching YM.Answer.ContinuumLimit WilsonGraphPaperPublication
open WilsonGraphPublishedReturnLaws
open scoped Classical
universe u

variable (g : GaugeGroup) (hg : g.IsSimple) (p : ℕ → ℕ) (hp : StrictMono p)
private abbrev selectedVision := publicPick.{u} g hg (ElectedPublication.order p hp)
private abbrev issuedDatum := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev electedPerspective := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev scoredMeasurement := CorrelationMatching.Construction.measurement (measurementOnPick.{u} g hg p hp)
private abbrev filedMeasurement := AppointedOrdinaryPacket.measurement hg (selectedVision.{u} g hg p hp) (issuedDatum g hg) (electedPerspective.{u} g hg)

theorem asFiled {n : ℕ} (r : ℝ) (h : ℕ) (a : Fin n → Label (maxwellReference g))
    (o : Spacetime) (x : YangMills.Points n) :
    OPEMatching.physicalOutput (scoredMeasurement.{u} g hg p hp) r h a o x = (filedMeasurement.{u} g hg p hp).wilsonOPE r h a o x := rfl

theorem packet {n : ℕ} (h : ℕ) (d : Fin n → ℕ) (v : (i : Fin n) → (maxwellReference g).sector (d i))
    (r : ℝ) (o : Spacetime) (x : YangMills.Points n) :
    OPEMatching.physicalOutput (scoredMeasurement.{u} g hg p hp) r h (fun i => ⟨d i, v i⟩) o x =
      (ElectedMeasurement.frame (selectedVision.{u} g hg p hp) (issuedDatum g hg) r h).symm
        ((selectedVision.{u} g hg p hp).pupil.P.packet h (fun i => o + r • x i)
          (fun i => ElectedMeasurement.frame (selectedVision.{u} g hg p hp) (issuedDatum g hg) r (d i) (v i)) o) :=
  (asFiled.{u} g hg p hp r h _ o x).trans (AppointedOrdinaryPacket.packet hg (selectedVision.{u} g hg p hp) (issuedDatum g hg) (electedPerspective.{u} g hg) h d v r o x)

end YM.Integration.WilsonFlashScoredOutput
end
