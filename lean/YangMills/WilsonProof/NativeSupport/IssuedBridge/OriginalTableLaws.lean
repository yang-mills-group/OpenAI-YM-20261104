import YangMills.WilsonProof.NativeSupport.IssuedBridge.ContinuumTableLaws
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PhysicalTableMultilinear
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PhysicalTableUnit
import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalPointReturns
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedBridge.OriginalTableLaws
open YangMills YangMills.Wilson YM.Integration
open YM.Extraction YM.FullVolume YM.PhysicalNext.Repeat.Legato
open Filter Function Set MeasureTheory
open scoped Topology
open IssuedBridge.PhysicalPeriodNodes IssuedBridge.OriginalPointReturns
variable {g : GaugeGroup}

theorem original (axis : YM.Axis) (hg : g.IsSimple) (B : Maxwell.Reference g)
    {ε : ℝ} (positive : 0 < ε) (σ : WilsonOriginalAllOrderCourse.Schedule g.core) :
    ∃ run : Construction g, WilsonRegularity run.family ∧ WilsonTrajectory B run.family ∧
      run.originalPointReturns ∧ ∃ D : WilsonData B run.family, ∀ (p : ℕ → ℕ) (hp : StrictMono p),
        let chosen := run.refine p hp
        Reconstruction.TableLaws chosen.hierarchy ∧ D.AdjointOn chosen.hierarchy ∧ run.family.Converges (p ∘ chosen.indices)
          (fun v => chosen.hierarchy.correlation none (chosen.hierarchy.project ∘ v)) := by
  obtain ⟨R,T,W,D0,trajectory,restored,banks,paid,bank,lamp,paths,low,oldRows,whole,make⟩ :=
    IssuedBridge.SelectedQuotient.original.{0} axis hg B positive σ
  obtain ⟨row,fixed,cluster⟩ := rows paid
  obtain ⟨selected,every⟩ := make (fun _ => True) (by intros; trivial)
  let D := IssuedRuns.FinalWilsonData.original R.family R.makes hg B
  refine ⟨FinalVolumeRecord.original R selected, D.regular, trajectory, ⟨appoint R.family row, fixed, ?_⟩, D, ?_⟩
  · intro p hp n v K compact inside ε pos
    let packet := selected ⟨p,hp⟩
    exact outer (GaugeGroup.coreSimple hg) packet.theory packet.reader row cluster n v K compact inside ε pos
  · intro p hp
    obtain ⟨adjoint,limit,_⟩ := every ⟨p,hp⟩
    exact ⟨tables (selected ⟨p,hp⟩).theory (selected ⟨p,hp⟩).reader,adjoint,limit⟩

end IssuedBridge.OriginalTableLaws
end
