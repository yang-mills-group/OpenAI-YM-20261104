import YangMills.WilsonProof.NativeSupport.CorrelationMatching.Construction.Estimates
import YM.Integration.WilsonGraphAppointedPosition

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace YangMills.CorrelationMatching.Construction

open YM.Integration YM.Answer.ContinuumLimit
open YM.Answer.ContinuumLimit.ElectedMeasurement
open WilsonGraphPaperPublication WilsonGraphPublishedReturnLaws
open scoped Classical Topology

universe u

/-- The normalized pre-frame gives an integrable signed triangle at every positive
radius. Its reading is exactly the measured coupling at every radius. -/
theorem measuredNormalization (g : GaugeGroup) (hg : g.IsSimple)
    (periods : ℕ → ℕ) (increasing : StrictMono periods) :
    let N := WilsonGraphGroupPositionReference.external g hg
    MeasuredNormalization N.menu N.realization
      (measurement (measurementOnPick.{u} g hg periods increasing)) := by
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let V := publicPick.{u} g hg (ElectedPublication.order periods increasing)
  let Q := WilsonGraphPaperPublication.perspective.{u} g hg
  let changeLaw := WilsonPositionHomogeneousCoefficients.purchased Z
    (_root_.IssuedBridge.PostedAppointedConversionFields.elected hg true)
  refine ⟨preFrame V Z, preNormalized hg V Q, preLocallyUnique hg V Q,
    preUnital V Z Q, preNested V Z Q, preReal V Z Q, ?_, ?_, ?_⟩
  · intro r positive
    exact preTriangleIntegrable hg V Z positive
  · intro r
    exact (congrFun (publicClock hg V Z Q) r).trans (publicTriangleClock hg V Q r)
  · intro d
    filter_upwards [numericalFrame V Z Q changeLaw d] with r received
    intro v
    change frame V Z r d v = preFrame V Z r d
      ((_root_.IssuedBridge.PostedNumericalAdjustment.filed Z changeLaw).value d (clock V Z r) v)
    exact received v

end YangMills.CorrelationMatching.Construction
