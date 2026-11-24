import YM.Integration.WilsonGraphPaperCorrelations
import YangMills.WilsonProof.NativeSupport.IssuedBridge.AllOriginalPhases

set_option autoImplicit false
noncomputable section

namespace YangMills.CorrelationMatching.Construction

open YM.Integration WilsonGraphPaperPublication
open YM.Answer.ContinuumLimit

universe u

/-- The completed vacuum sectors belong to the field table on the selected
volume refinement. They give the reconstruction of that same hierarchy. -/
theorem physicalHierarchy (g : GaugeGroup) (hg : g.IsSimple)
    (periods : ℕ → ℕ) (increasing : StrictMono periods) :
    let run := WilsonGraphPaperPublication.issued.{u}.runs g hg
    let T := (run.refine periods increasing).hierarchy
    T.Reconstructed ∧ Reconstruction.TableLaws T ∧ Nonempty (Reconstruction.Phases T) := by
  let V := publicPick.{u} g hg (ElectedPublication.order periods increasing)
  exact ⟨publicReconstruction V.pupil.last V.pupil.P V.pupil.L V.pupil.phase,
    _root_.IssuedBridge.OriginalTableLaws.tables V.pupil.last V.pupil.P,
    ⟨_root_.IssuedBridge.AllOriginalPhases.phases V.pupil.last V.pupil.P V.pupil.L V.pupil.phase⟩⟩

end YangMills.CorrelationMatching.Construction
end
