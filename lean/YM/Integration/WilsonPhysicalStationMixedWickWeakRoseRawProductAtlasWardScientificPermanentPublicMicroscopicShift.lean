import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicFullUV

noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicMicroscopicShift
open Function Filter Set Lattice Wilson RG Source Table Spec
open scoped Classical Topology
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true

def translated {G:Gauge}{n:Side}(b:Site n)(U:Config G n):Config G n:=
  fun e=>U (e.1+b,e.2)

theorem placed {G:Gauge}{n:Side}(x b:Site n)(U:Config G n):
    expandAt (x+b) U=expandAt x (translated b U):=by
  funext i
  change U (wrap n i.1+(x+b),i.2)=U ((wrap n i.1+x)+b,i.2)
  rw [add_assoc]

theorem original {G:Gauge}(C:Family G)(N p:ℕ){d:ℕ}(v:(C.labels.level d).Coeff)
    (x b:Site (C.side N p))(U:Config G (C.side N p)):
    C.O N p v (x+b) U=C.O N p v x (translated b U):=by
  unfold Family.O Source.TransferData.cylinder Source.initial Source.SectionData.places
  change ((C.S.a N:ℂ)^d)⁻¹ • (C.localSection d).evaluate _ (expandAt (x+b) U) = _
  rw [placed]
  rfl

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicMicroscopicShift
end
