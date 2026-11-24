import YM.Nonperturbative.HeadlineSpec
import YangMills.WilsonProof.Hierarchy
import YangMills.WilsonProof.NativeSupport.HierarchyBridge
import YangMills.Phases
import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalObservablePhases

/-! Observable separation and signed train moments for the Wilson hierarchy. -/

set_option autoImplicit false
noncomputable section

namespace IssuedBridge.PhaseCorrelations
open YangMills YangMills.Wilson YM YM.Spec YM.OPE.Orbits
open Filter Set MeasureTheory
open scoped Topology BigOperators
variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable {B : YangMills.Maxwell.Reference g}

theorem law (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (D : WilsonData B (wilsonFamily C)) (originalStar : D.starToken = C.book.reflectedToken YM.timeAxis) :
    ObservablePhases.Law D (hierarchy F Q) := by
  exact _root_.IssuedBridge.OriginalObservablePhases.original F Q D originalStar
end IssuedBridge.PhaseCorrelations

end
