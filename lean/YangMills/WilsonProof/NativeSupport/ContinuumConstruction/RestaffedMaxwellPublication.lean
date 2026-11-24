import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.ElectedMaxwellLaws
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.RestaffedMeasuredStress
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 8192
noncomputable section
namespace YM.Answer.ContinuumLimit.RestaffedMaxwellPublication
open Function Filter Set Integration Integration.Election Lattice RG Wilson Extraction Climb Spec
open Trace.Pilot PhysicalNext.Repeat.Legato OPE OPE.Orbits PhysMS PhysMS.Frame XSpace XSpace.Normalize FVA2 FVA2.Register
open scoped Topology BigOperators Classical
universe u
variable {g : YangMills.GaugeGroup} {H : g.core.Simple} {ε : ℝ} {e : Axis} {O : OrderS g.core}
  {E : Construction.{u} H ε e O} {ξ : Extraction.Order}


theorem inputs (V : Vision E ξ) (Z : WilsonPrescription g.core) {lamp : Bool}
    (Q : Perspective H Z lamp) :
    PublishedMixedMaxwell.Inputs V.pupil.last V.pupil.P V.pupil.J V.pupil.H Z H where
  facilities := V.pupil.pillar
  leading := V.pupil.VFrame.2
  obeys := V.pupil.VFrame.1
  viewer := @fun _ _ v j K hK sep δ pos => PublishedFrameTransfers.viewerZero V Z Q v j K hK sep δ pos
  stress := RestaffedMeasuredStress.postStress V Z

def scaling (V : Vision E ξ) (Z : WilsonPrescription g.core) {lamp : Bool} (Q : Perspective H Z lamp) :
    (YangMills.hierarchy V.pupil.last V.pupil.P).MaxwellScaling (YangMills.maxwellReference g) :=
  YangMills.PublishedFrameLaws.scaling Z (inputs V Z Q) V.sc

theorem radii (V : Vision E ξ) (Z : WilsonPrescription g.core) {lamp : Bool} (Q : Perspective H Z lamp) :
    (scaling V Z Q).r = V.sc.r := rfl

theorem frames (V : Vision E ξ) (Z : WilsonPrescription g.core) {lamp : Bool}
    (Q : Perspective H Z lamp) (k : ℕ) :
    (scaling V Z Q).frame k = ElectedMaxwellLaws.publicFrame V Z (V.sc.r k) := rfl

theorem fixed (V : Vision E ξ) (Z : WilsonPrescription g.core) {lamp : Bool} (Q : Perspective H Z lamp) :
    YangMills.FixedFields.Laws (YangMills.maxwellReference g) (YangMills.hierarchy V.pupil.last V.pupil.P)
      (scaling V Z Q) := YangMills.PublishedFrameLaws.fixed Z (inputs V Z Q) V.sc

theorem allRadii (V : Vision E ξ) (Z : WilsonPrescription g.core) {lamp : Bool} (Q : Perspective H Z lamp) :
    YangMills.AllRadii.Laws (YangMills.maxwellReference g) (YangMills.hierarchy V.pupil.last V.pupil.P)
      (scaling V Z Q) (ElectedMaxwellLaws.publicFrame V Z) :=
  YangMills.PublishedFrameLaws.allRadii Z (inputs V Z Q) V.sc

theorem bounds (V : Vision E ξ) (Z : WilsonPrescription g.core) {lamp : Bool} (Q : Perspective H Z lamp) :
    YangMills.AllRadii.FrameBounds (YangMills.maxwellReference g) (YangMills.hierarchy V.pupil.last V.pupil.P)
      (scaling V Z Q) (ElectedMaxwellLaws.publicFrame V Z) :=
  YangMills.PublishedFrameLaws.bounds Z (inputs V Z Q) V.sc

theorem original (V : Vision E ξ) (Z : WilsonPrescription g.core) {lamp : Bool} (Q : Perspective H Z lamp) :
    let B := YangMills.maxwellReference g
    let T := YangMills.hierarchy V.pupil.last V.pupil.P
    ∃ X : T.MaxwellScaling B, X.r = V.sc.r ∧ (∀ k, X.frame k = ElectedMaxwellLaws.publicFrame V Z (V.sc.r k)) ∧
      YangMills.FixedFields.Laws B T X ∧ YangMills.AllRadii.Laws B T X (ElectedMaxwellLaws.publicFrame V Z) ∧
      YangMills.AllRadii.FrameBounds B T X (ElectedMaxwellLaws.publicFrame V Z) :=
  ⟨scaling V Z Q,radii V Z Q,frames V Z Q,fixed V Z Q,allRadii V Z Q,bounds V Z Q⟩

end YM.Answer.ContinuumLimit.RestaffedMaxwellPublication
end
