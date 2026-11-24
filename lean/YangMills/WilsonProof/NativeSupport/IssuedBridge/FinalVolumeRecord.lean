import YangMills.WilsonProof.NativeSupport.WilsonConstruction
import YangMills.WilsonProof.NativeSupport.IssuedBridge.SelectedQuotient
noncomputable section
namespace IssuedBridge.FinalVolumeRecord
open YM YM.Integration
open YangMills YangMills.Wilson
open YM.PhysicalNext.Repeat.Legato
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
variable {g : GaugeGroup}

def original (R : Run g.core)
    (selected : (request : YM.Extraction.Sequence) →
      WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicEndowment.Published R request) :
    Construction g where
  family := wilsonFamily R.family
  refine p hp :=
    let packet := selected ⟨p,hp⟩
    ⟨packet.daughter.per.choose, packet.daughter.per.monotone, hierarchy packet.theory packet.reader⟩

theorem funded (axis : YM.Axis) (hg : g.IsSimple) (B : Maxwell.Reference g)
    {ε : ℝ} (positive : 0 < ε) (σ : WilsonOriginalAllOrderCourse.Schedule g.core) :
    ∃ run : Construction g, WilsonRegularity run.family ∧ WilsonTrajectory B run.family ∧
      ∃ D : WilsonData B run.family, ∀ (p : ℕ → ℕ) (hp : StrictMono p),
        let choice := run.refine p hp
        D.AdjointOn choice.hierarchy ∧
        run.family.Converges (p ∘ choice.indices)
          (fun v => choice.hierarchy.correlation none (choice.hierarchy.project ∘ v)) := by
  obtain ⟨R,T,W,D0,trajectory,restored,banks,paid,bank,lamp,paths,low,row,whole,make⟩ :=
    IssuedBridge.SelectedQuotient.original.{0} axis hg B positive σ
  obtain ⟨selected, every⟩ := make (fun _ => True) (by intros; trivial)
  let D := IssuedRuns.FinalWilsonData.original R.family R.makes hg B
  refine ⟨original R selected, D.regular, trajectory, D, ?_⟩
  intro p hp
  obtain ⟨adjoint, limit, _⟩ := every ⟨p,hp⟩
  exact ⟨adjoint, limit⟩

end IssuedBridge.FinalVolumeRecord
end
