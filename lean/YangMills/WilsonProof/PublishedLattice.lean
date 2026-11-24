import YangMills.WilsonProof.Mesh
import YM.Integration.WilsonGraphIncumbentGraphPublication

set_option autoImplicit false
noncomputable section
namespace YangMills.WilsonProof
open PerturbativeMatching
open YM.Integration YM.Integration.WilsonGraphPaperPublication
open _root_.IssuedBridge.PhysicalPeriodNodes

abbrev publishedRun (g : GaugeGroup) (hg : g.IsSimple) : Wilson.Construction g :=
  (WilsonGraphPaperPublication.issued.{0}).runs g hg

abbrev publishedLattice (g : GaugeGroup) (hg : g.IsSimple) :
    Wilson.WilsonData (maxwellReference g) (publishedRun g hg).family :=
  let E := construction.{0} g hg
  _root_.IssuedRuns.FinalWilsonData.original E.paths.family E.paths.makes hg (maxwellReference g)

abbrev publishedKernels (g : GaugeGroup) (hg : g.IsSimple) :
    Wilson.PeriodPointTable (publishedRun g hg).family :=
  appoint (construction.{0} g hg).paths.family (rowBefore.{0} g hg).choose

theorem admissibleOnPublishedLattice (g : GaugeGroup) (hg : g.IsSimple) :
    AdmissibleLattice (publishedLattice g hg) := by
  let E := construction.{0} g hg
  exact ⟨E.paths.family, rfl, E.paths.makes, fun _ => rfl, fun _ _ => rfl⟩

theorem smoothOnPublishedLattice (g : GaugeGroup) (hg : g.IsSimple) :
    SmoothMeshLimit (publishedRun g hg).family (publishedKernels g hg) :=
  smoothOnAppointedRow (construction.{0} g hg).paths.family (rowBefore.{0} g hg).choose
    (publicPick.{0} g hg YM.Extraction.Order.full).pupil.TrackU
    (rowBefore.{0} g hg).choose_spec.2.1

end YangMills.WilsonProof
