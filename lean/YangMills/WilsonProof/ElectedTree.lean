import YangMills.WilsonProof.TreeUniform
import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometryElection

set_option autoImplicit false
noncomputable section
namespace YangMills.WilsonProof
open YM YM.Integration YM.Answer.ContinuumLimit

/-- The tested tree bounds use the reader retained by this particular period refinement. -/
theorem powerTreesOnPublishedRefinement (g : GaugeGroup) (hg : g.IsSimple)
    (periods : ℕ → ℕ) (increasing : StrictMono periods) :
    Hierarchy.PowerTreeExpansion (((WilsonGraphPaperPublication.issued.{0}.runs g hg).refine periods increasing).hierarchy) := by
  let V := WilsonGraphPaperPublication.publicPick.{0} g hg (ElectedPublication.order periods increasing)
  obtain ⟨selected, _, _, _, _, _, uniform, _⟩ :=
    WilsonSharpPhysicalTreeGeometryElection.retained.{0} g hg periods increasing
  rw [selected]
  exact WilsonSharpPhysicalTreeGeometry.onFiledUniform V.pupil.last V.pupil.P uniform

end YangMills.WilsonProof
