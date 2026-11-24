import YangMills.WilsonProof.NativeSupport.IssuedBridge.PhysicalTableMultilinear
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PhysicalTableUnit

set_option autoImplicit false
noncomputable section
namespace IssuedBridge.OriginalTableLaws
open YangMills
variable {g : GaugeGroup}

theorem tables {C : YM.Family g.core} {o : YM.Extraction.Order} {S : YM.Table C.book}
    (F : YM.Spec.Final C o S) (Q : YM.OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) :
    Reconstruction.TableLaws (hierarchy F Q) where
  filtration := PhysicalTableLabels.filtration F Q
  unitInGrade := PhysicalTableLabels.unitInGrade F Q
  multilinear := PhysicalTableMultilinear.original F Q
  empty := PhysicalTableLabels.empty F Q
  unit s := fun {_} v => PhysicalTableUnit.original F Q s v

end IssuedBridge.OriginalTableLaws
end
