import YangMills.ScalingLimits
import YangMills.WilsonProof.NativeSupport.FixedFieldExistence

/-! The all-radii Maxwell comparison on each selected Wilson hierarchy. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.AllRadii
open Filter Set
open scoped Topology BigOperators
variable {g : GaugeGroup} {C : WilsonFamily g} (B : Maxwell.Reference g) (T : Hierarchy C)





def ExistsAt (run : _root_.YangMills.Wilson.Construction g) : Prop :=
  _root_.YangMills.Wilson.ExistsAt B run ∧ ∀ (p : ℕ → ℕ) (hp : StrictMono p), let T := (run.refine p hp).hierarchy
    ∃ (X : T.MaxwellScaling B) (J : ℝ → Frame B T), FixedFields.Laws B T X ∧ Laws B T X J

def Score : Prop := ∃ pub : _root_.YangMills.Wilson.Publication, ∀ (g : GaugeGroup) (hg : g.IsSimple),
  ExistsAt (pub.coordinates g hg) (pub.runs g hg)

theorem implies_v23 (h : Score) : FixedFields.Score := by
  obtain ⟨pub, runs⟩ := h
  refine ⟨pub, fun g hg => ⟨(runs g hg).1, fun p hp => ?_⟩⟩
  obtain ⟨X, _, prev, _⟩ := (runs g hg).2 p hp
  exact ⟨X, prev.selected, prev⟩

end YangMills.AllRadii
