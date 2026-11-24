import YM.Integration.WilsonGraphPaperCorrelations
import YM.Independent.Core
import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalWardLaws
import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalTraceTest

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable section
namespace YangMills.CorrelationMatching.Construction

open YM.Integration
open WilsonGraphPaperPublication

/-- The OPE, stress Ward identities and trace test use the fields of the
same volume refinement as the measured correlation functions. -/
theorem localLaws (g : GaugeGroup) (hg : g.IsSimple)
    (periods : ℕ → ℕ) (strict : StrictMono periods) :
    let run := WilsonGraphPaperPublication.issued.{0}.runs g hg
    let T := (run.refine periods strict).hierarchy
    T.OperatorProductExpansion ∧ Nonempty T.StressWardLaws ∧ T.TraceTest := by
  let order := YM.Answer.ContinuumLimit.ElectedPublication.order periods strict
  let V := publicPick.{0} g hg order
  let F := V.pupil.last
  let Q := V.pupil.P
  have selected := ((rowBefore.{0} g hg).choose_spec.2.2
    (fun _ => True) (fun _ _ _ => True.intro)).choose_spec
  obtain ⟨_, _, _, _, _, traceResult, _, _⟩ := selected.1 order
  let core := YM.Independent.Core.of_receipts.{0,0} (simple g hg) F V.pupil.L Q
    V.pupil.phase traceResult V.pupil.pillar.toServices V.pupil.foundation
  have ope : YM.Nonperturbative.Headline.SeparatedOPE F Q := by
    refine ⟨core.ope.coefficients, ?_, core.joint⟩
    intro I J _ _ d e a b M η c δ hM hη hc hδ D
    exact core.point a b hM hη hc hδ D
  have trace : YM.Nonperturbative.Headline.TraceExclusions.{0,0} F :=
    ⟨core.trace.centered, core.trace.identified, core.trace.shortDistance,
      core.trace.positive, core.trace.wick,
      fun n U physical unit translations => core.trace.maxwell n U ⟨physical, unit, translations⟩,
      core.trace.invariant⟩
  exact ⟨publicOPE F Q ope, ⟨IssuedPhysical.publicWards F Q⟩,
    IssuedPhysical.publicTrace F Q hg trace⟩

end YangMills.CorrelationMatching.Construction
end
