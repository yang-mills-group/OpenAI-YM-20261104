import YangMills.WilsonProof.NativeSupport.IssuedBridge.GroupSelectedJets
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedBridge.FullPhysicalReconstruction
open YangMills YangMills.Wilson YM.Integration
open YM.Extraction YM.FullVolume YM.PhysicalNext.Repeat.Legato
open Filter Function Set MeasureTheory
open scoped Topology
open IssuedBridge.PhysicalPeriodNodes IssuedBridge.OriginalPointReturns
variable {g : GaugeGroup}

theorem original (axis : YM.Axis) (hg : g.IsSimple)
    {ε : ℝ} (positive : 0 < ε) (σ : WilsonOriginalAllOrderCourse.Schedule g.core) :
    let B := IssuedMaxwell.Reference.issued g
    ∃ run : Construction g, WilsonRegularity run.family ∧ WilsonTrajectory B run.family ∧
      run.originalPointReturns ∧ ∃ D : WilsonData B run.family, ∀ (p : ℕ → ℕ) (hp : StrictMono p),
        let chosen := run.refine p hp
        WilsonReconstruction B chosen.hierarchy ∧ chosen.hierarchy.Reconstructed ∧
        D.AdjointOn chosen.hierarchy ∧ run.family.Converges (p ∘ chosen.indices)
          (fun v => chosen.hierarchy.correlation none (chosen.hierarchy.project ∘ v)) := by
  let B := IssuedMaxwell.Reference.issued g
  obtain ⟨R,T,W,D0,trajectory,restored,banks,paid,bank,lamp,paths,low,oldRows,whole,make⟩ :=
    IssuedBridge.SelectedQuotient.original.{0} axis hg B positive σ
  obtain ⟨row,fixed,cluster⟩ := rows paid
  obtain ⟨selected,every⟩ := make (fun _ => True) (by intros; trivial)
  let D := IssuedRuns.FinalWilsonData.original R.family R.makes hg B
  refine ⟨FinalVolumeRecord.original R selected, D.regular, trajectory, ⟨appoint R.family row, fixed, ?_⟩, D, ?_⟩
  · intro p hp n v K compact inside δ pos
    let packet := selected ⟨p,hp⟩
    exact outer (GaugeGroup.coreSimple hg) packet.theory packet.reader row cluster n v K compact inside δ pos
  · intro p hp
    let packet := selected ⟨p,hp⟩
    obtain ⟨adjoint,limit,chosen,_,_,_,_,_,_,_,_,first,_,_,_,_,marked,_⟩ := every ⟨p,hp⟩
    refine ⟨⟨OriginalTableLaws.tables packet.theory packet.reader,
      ⟨AllOriginalPhases.phases packet.theory packet.reader packet.atlas chosen.phases⟩,
      ⟨IssuedPhysical.issuedScaling packet.theory packet.reader _ first,
       IssuedPhysical.selectedScaling packet.theory packet.reader _ first marked⟩⟩,
      publicReconstruction packet.theory packet.reader packet.atlas chosen.phases,adjoint,limit⟩
end IssuedBridge.FullPhysicalReconstruction
end
