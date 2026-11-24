import YangMills.WilsonProof.PhaseAwards
import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalPhaseContours
import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalPhaseUnits

set_option autoImplicit false
noncomputable section
namespace IssuedBridge.AllOriginalPhases
open YangMills
open scoped Topology
variable {g : GaugeGroup}

def phases {C : YM.Family g.core} {o : YM.Extraction.Order} {S : YM.Table C.book}
    (F : YM.Spec.Final C o S) (Q : YM.OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (L : YM.EveryPhase.Almanac F) (valid : YM.EveryPhase.Completed F L) :
    Reconstruction.Phases (hierarchy F Q) where
  phaseTheory := OriginalPhaseContours.actor F Q L
  continuedStress := WilsonProof.PhaseAwards.continuedStress Q L
  source i := OriginalPhaseContours.source F Q L valid i (fun t => OriginalPhaseUnits.op_unit F L i t 4)
  selectedTheory := congrArg (fun a : YM.Boundary.Wightman S =>
    (⟨stateSpace a,view a⟩ : Σ H : HilbertSpace, WightmanTheory H (hierarchy F Q).labels)) L.baseR
  selectedTube n v z _ space := by
    change (L.contours F.α.atPoint).waves.F n z space (fun j => S.pin (v j).1 (v j).2) =
      F.A.waves.F n z space (fun j => S.pin (v j).1 (v j).2)
    rw [L.baseB]
  characterContinuity := valid.depends

end IssuedBridge.AllOriginalPhases
end
