import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalWardLaws
import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalTraceTest
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedGroupCalendar
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedBridge.FullPhysicalProperties
open YangMills YangMills.Wilson YM.Integration
open YM.Extraction YM.FullVolume YM.PhysicalNext.Repeat.Legato
open Filter Function Set MeasureTheory
open scoped Topology
open IssuedBridge.PhysicalPeriodNodes IssuedBridge.OriginalPointReturns
variable {g : GaugeGroup}

theorem original (hg : g.IsSimple) :
    let B := IssuedMaxwell.Reference.issued g
    ∃ run : Construction g, WilsonRegularity run.family ∧ WilsonTrajectory B run.family ∧
      run.originalPointReturns ∧ ∃ D : WilsonData B run.family, ∀ (p : ℕ → ℕ) (hp : StrictMono p),
        let chosen := run.refine p hp
        chosen.hierarchy.Properties B (p ∘ chosen.indices) ∧ WilsonReconstruction B chosen.hierarchy ∧ D.AdjointOn chosen.hierarchy := by
  let B := IssuedMaxwell.Reference.issued g
  obtain ⟨R,T,W,D0,trajectory,restored,banks,paid,bank,lamp,paths,low,oldRows,whole,make⟩ :=
    IssuedBridge.SelectedQuotient.original.{0} YM.timeAxis hg B (ε:=1) zero_lt_one (PostedGroupCalendar.schedule g)
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
    let core := YM.Independent.Core.of_receipts.{0,0} (GaugeGroup.coreSimple hg)
      packet.theory packet.atlas packet.reader chosen.phases chosen.trace chosen.facilities.toServices chosen.foundation
    have ope : YM.Nonperturbative.Headline.SeparatedOPE packet.theory packet.reader := by
      refine ⟨core.ope.coefficients, ?_, core.joint⟩
      intro I K _ _ d e a b M η c δ hM hη hc hδ D
      exact core.point a b hM hη hc hδ D
    have trace : YM.Nonperturbative.Headline.TraceExclusions.{0,0} packet.theory :=
      ⟨core.trace.centered,core.trace.identified,core.trace.shortDistance,core.trace.positive,core.trace.wick,
        fun n U physical unit translations => core.trace.maxwell n U ⟨physical,unit,translations⟩,core.trace.invariant⟩
    let scale := IssuedPhysical.issuedScaling packet.theory packet.reader _ first
    exact ⟨⟨limit,publicReconstruction packet.theory packet.reader packet.atlas chosen.phases,
      publicOPE packet.theory packet.reader ope,⟨IssuedPhysical.publicWards packet.theory packet.reader⟩,
      IssuedPhysical.publicTrace packet.theory packet.reader hg trace,⟨scale⟩⟩,
      ⟨OriginalTableLaws.tables packet.theory packet.reader,
      ⟨AllOriginalPhases.phases packet.theory packet.reader packet.atlas chosen.phases⟩,
      ⟨scale,IssuedPhysical.selectedScaling packet.theory packet.reader _ first marked⟩⟩,adjoint⟩
end IssuedBridge.FullPhysicalProperties
end
