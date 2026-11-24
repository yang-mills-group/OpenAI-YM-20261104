import YangMills.ScalingLimits
import YangMills.WilsonProof.NativeSupport.AllRadiiExistence

/-! Engineering powers for the all-radii frame on the physical field filtration. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.AllRadii
open Filter
open scoped Topology BigOperators
variable {g : GaugeGroup} {C : WilsonFamily g} (B : Maxwell.Reference g) (T : Hierarchy C)



def NormalizedAt (run : _root_.YangMills.Wilson.Construction g) : Prop :=
  _root_.YangMills.Wilson.ExistsAt B run ∧ ∀ (p : ℕ → ℕ) (hp : StrictMono p), let T := (run.refine p hp).hierarchy
    ∃ (X : T.MaxwellScaling B) (J : ℝ → Frame B T),
      FixedFields.Laws B T X ∧ Laws B T X J ∧ FrameBounds B T X J

def NormalizedScore : Prop := ∃ pub : _root_.YangMills.Wilson.Publication, ∀ (g : GaugeGroup) (hg : g.IsSimple),
  NormalizedAt (pub.coordinates g hg) (pub.runs g hg)

theorem implies_v24 (h : NormalizedScore) : Score := by
  obtain ⟨pub, runs⟩ := h
  refine ⟨pub, fun g hg => ⟨(runs g hg).1, fun p hp => ?_⟩⟩
  obtain ⟨X, J, old, all, _⟩ := (runs g hg).2 p hp
  exact ⟨X, J, old, all⟩

end YangMills.AllRadii
