import YangMills.WilsonProof.NativeSupport.WilsonConstruction
import YangMills.WilsonProof.NativeSupport.WilsonLatticeData
import YangMills.WilsonProof.NativeSupport.WilsonReconstruction
import YangMills.WilsonProof.NativeSupport.WilsonTrajectory
import YangMills.WilsonProof.NativeSupport.ObservablePhases
import YangMills.WilsonProof.NativeSupport.OriginalPointReturns

/-! The existence award on named data. The selected continuum hierarchy can be
reused by the matching award. Volume uniqueness is not part of the statement. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.Wilson

def ExistsAt {g : GaugeGroup} (B : Maxwell.Reference g) (run : Construction g) : Prop :=
  (WilsonRegularity run.family ∧ WilsonTrajectory B run.family ∧ run.originalPointReturns) ∧
  ∃ D : WilsonData B run.family,
    ∀ (p : ℕ → ℕ) (hp : StrictMono p),
      let choice := run.refine p hp
      choice.hierarchy.Properties B (p ∘ choice.indices) ∧
      WilsonReconstruction B choice.hierarchy ∧ D.AdjointOn choice.hierarchy ∧
      ObservablePhases.Law D choice.hierarchy

def ExistenceOn (published : Publication) : Prop :=
  ∀ (g : GaugeGroup) (hg : g.IsSimple), ExistsAt (published.coordinates g hg) (published.runs g hg)

def ExistenceScore : Prop := ∃ published : Publication, ExistenceOn published

theorem existenceScore_implies_jointExistence (h : ExistenceScore) : JointExistence := by
  obtain ⟨published, funded⟩ := h
  intro g hg
  obtain ⟨regular, _, all⟩ := funded g hg
  refine ⟨published.coordinates g hg, (published.runs g hg).family, regular.1, ?_⟩
  intro p hp
  let choice := (published.runs g hg).refine p hp
  exact ⟨choice.indices, choice.increasing, choice.hierarchy, (all p hp).1⟩

end YangMills.Wilson
