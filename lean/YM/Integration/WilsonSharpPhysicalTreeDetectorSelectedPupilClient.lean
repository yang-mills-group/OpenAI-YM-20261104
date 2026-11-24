import YM.Integration.WilsonSharpPhysicalTreeDetectorApplication
import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometryElection

set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonSharpPhysicalTreeDetectorSelectedPupilClient
open Filter Spec OPE OPE.Log Answer.ContinuumLimit Answer.ContinuumLimit.PreElectedPublication
open WilsonGraphPaperPublication WilsonSharpPhysicalTreeDetectorApplication
open scoped Classical Topology

/-- Fresh application of the full physical detector theorem to the exact reader,
filter and matrix owned by this literal public refinement. -/
theorem original (g : YangMills.GaugeGroup) (hg : g.IsSimple) (p : ℕ → ℕ) (hp : StrictMono p) :
    let ξ := ElectedPublication.order p hp
    let E := construction.{u} g hg
    let V := publicPick.{u} g hg ξ
    (((issued.{u}).runs g hg).refine p hp).hierarchy = YangMills.hierarchy V.pupil.last V.pupil.P ∧
    (V.pupil.Y : Filter (ℕ × ℕ)) ≤ V.pupil.f.fuse ∧
    MatrixTicket (C := E.paths.family) V.pupil.S V.pupil.last.sector.derivatives (V.pupil.Y : Filter _) ∧
    AllTrees V.pupil.last V.pupil.P := by
  let ξ := ElectedPublication.order p hp
  let V := publicPick.{u} g hg ξ
  obtain ⟨hierarchy,_,fac,_,lo,ticket,_,trace⟩ := WilsonSharpPhysicalTreeGeometryElection.retained.{u} g hg p hp
  exact ⟨hierarchy,lo,ticket,same_reader V.pupil.last V.pupil.P fac.toServices trace⟩

end YM.Integration.WilsonSharpPhysicalTreeDetectorSelectedPupilClient
