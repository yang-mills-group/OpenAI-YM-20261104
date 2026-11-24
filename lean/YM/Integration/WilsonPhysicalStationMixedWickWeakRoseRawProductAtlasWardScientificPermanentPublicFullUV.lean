import YM.Integration.WilsonPhysicalCommonElection
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicPeriodMesh

/-! Full fixed-period cutoff limits for the appointed physical fields tested at a fixed radius. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicFullUV
open Filter Set Spec Table Extraction Next.UVStress
open PhysicalNext.Repeat.Legato
open PhysMS
open scoped Classical Topology BigOperators
universe u
variable {G : Gauge} {R : Run G} {T : Campaign R} {W : Campaign.Pillars R T}
    {order : Extraction.Order} {S : Table R.family.book}

theorem original {axis:Axis}{simple:G.Simple}{ε:ℝ}{s:WilsonOriginalAllOrderCourse.Schedule G}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε s R T W)(F:Final R.family order S):
    (⟨.full,order.per⟩:Extraction.Order).Ordered R.family S:=by
  have full:=FullVolume.Final.from_spec order ⟨F⟩
    (WilsonPhysicalCommonElection.finances paid).1.2.1.jewel.fullMesh
  exact ⟨fun n tokens test=>full.reads n tokens test⟩

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicFullUV
end
