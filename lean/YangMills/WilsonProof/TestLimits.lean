import YangMills.PerturbativeMatching.VolumeLimits

noncomputable section
namespace YangMills.WilsonProof
open Filter PerturbativeMatching
open scoped Topology

theorem testLimitsOnRefinement {g : GaugeGroup} {C : WilsonFamily g}
    {T : Hierarchy C} {p q : ℕ → ℕ} (increasing : StrictMono q)
    (selected : C.Converges (p ∘ q) (fun v => T.correlation none (T.project ∘ v))) :
    RepresentsTestLimits T p := by
  intro L original n v t
  obtain ⟨_, source, sourceUV, sourceVolume⟩ := original n v t
  obtain ⟨suitable, target, targetUV, targetVolume⟩ := selected n v t
  have rows : (fun k => source ((p ∘ q) k)) =ᶠ[atTop] (fun k => target ((p ∘ q) k)) :=
    suitable.mono fun k hk => tendsto_nhds_unique (sourceUV _ hk) (targetUV _ hk)
  exact tendsto_nhds_unique ((sourceVolume.comp increasing.tendsto_atTop).congr' rows) targetVolume

end YangMills.WilsonProof
