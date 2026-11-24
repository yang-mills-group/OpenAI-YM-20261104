import YM.Integration.WilsonGraphPaperCorrelations
import YangMills.WilsonProof.NativeSupport.WilsonFlashScoredGroupReference
import YangMills.WilsonProof.NativeSupport.WilsonFlashScoredOutput
import YangMills.WilsonProof.NativeSupport.WilsonFlashScoredWholeFieldMass
import YM.Integration.WilsonGraphAppointedOrdinaryTestedExpansion
import YangMills.WilsonProof.NativeSupport.OPEMatching.Estimates

noncomputable section
namespace YM.Integration.WilsonFlashScoredOrdinaryEstimates
open YangMills YangMills.Matching Filter YM.Answer.ContinuumLimit
open GradedFar WilsonGraphPublishedReturnLaws
open scoped BigOperators Topology Classical
universe u

variable (g : GaugeGroup) (hg : g.IsSimple)
private abbrev table := OPEMatching.reference g (WilsonFlashScoredGroupReference.determined g hg)
private abbrev conversion := (WilsonFlashScoredGroupReference.normalization g hg).conversion.conversion

theorem converted {n : ℕ} (h k : ℕ) (a : Fin n → Label (maxwellReference g)) (x : YangMills.Points n) :
    (conversion g hg).ope (table g hg) h k a x =
      (AppointedGraphOrdinaryConversion.filedConversion g hg).ope
        (_root_.IssuedMaxwell.GraphCoefficients.issued g) h k a x := by
  have transport (A B : MSbar.Coefficients (maxwellReference g)) (same : A.ope = B.ope) :
      (conversion g hg).ope A h k a x = (conversion g hg).ope B h k a x := by
    rcases A with ⟨ca, oa⟩
    rcases B with ⟨cb, ob⟩
    change oa = ob at same
    subst ob
    rfl
  exact transport _ _ (WilsonFlashScoredGroupReference.issued g hg)

variable (periods : ℕ → ℕ) (mono : StrictMono periods)
private abbrev measurement := CorrelationMatching.Construction.measurement
  (measurementOnPick.{u} g hg periods mono)

private abbrev filedReader := AppointedOrdinaryPacket.measurement hg
  (WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods mono))
  (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)
  (WilsonGraphPaperPublication.perspective.{u} g hg)

theorem clock : (measurement.{u} g hg periods mono).coupling =
    (filedReader.{u} g hg periods mono).clock := rfl

theorem estimates (income : ∀ n h, AppointedOrdinaryPurchases.AtOutput.{u} g hg periods mono n h) :
    OPEMatching.Estimates (table g hg) (conversion g hg) (measurement.{u} g hg periods mono) := by
  classical
  let H := measurement.{u} g hg periods mono
  refine ⟨?_, ?_, ?_⟩
  · intro n h d
    refine ⟨0, fun v o out => ?_⟩
    simpa only [WilsonFlashScoredOutput.asFiled, clock, converted] using
      (AppointedOrdinaryPurchases.tested g hg periods mono (income n h) d v o out)
  · intro n h p d o K compact separated
    obtain ⟨A, hA, event⟩ := income n h p 0 d K compact separated
    refine ⟨A, hA, ?_⟩
    filter_upwards [event] with r paid
    intro v x hx
    let a : Fin n → Label (maxwellReference g) := fun i => ⟨d i, v i⟩
    let residual := OPEMatching.physicalOutput H r h a o x -
      OPEMatching.prediction (table g hg) (conversion g hg) h p (H.coupling r) a x
    obtain ⟨out, contractive, reads⟩ := WilsonFlashScoredWholeFieldMass.attained residual
    change sectorMass residual ≤ _
    rw [← reads]
    dsimp only [residual]
    rw [map_sub]
    simpa only [H, WilsonFlashScoredOutput.asFiled, clock, OPEMatching.prediction, converted] using
      (CorrelationOnly.shapeValue (paid v o x hx out contractive))
  · intro n h p j d K compact separated
    simpa only [WilsonFlashScoredOutput.asFiled, clock, OPEMatching.prediction, converted] using
      (income n h p j d K compact separated)

end YM.Integration.WilsonFlashScoredOrdinaryEstimates
end
