import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalPhaseSeparation
import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalAdjointTrain
import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalTrainMoments
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.OriginalObservablePhases
open YangMills YangMills.Wilson YM YM.Spec YM.OPE.Orbits
open Filter Set MeasureTheory
open scoped Topology BigOperators
variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable {B : YangMills.Maxwell.Reference g}

theorem original (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (D : WilsonData B (wilsonFamily C)) (originalStar : D.starToken = C.book.reflectedToken YM.timeAxis) :
    ObservablePhases.Law D (hierarchy F Q) := by
  refine ⟨OriginalPhaseSeparation.original F Q, ?_⟩
  intro k w adjoint
  simp only [OriginalAdjointTrain.train D originalStar, ← OriginalAdjointTrain.readSigned F Q]
  exact OriginalTrainMoments.original F Q (fun j => OriginalAdjointTrain.signed (w j) (adjoint j))
end IssuedBridge.OriginalObservablePhases
end
