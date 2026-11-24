import YangMills.WilsonProof.PublicView
import YangMills.WilsonProof.WilsonBridge
import YM.OPE.Nesting.Endpoint

set_option autoImplicit false
noncomputable section
namespace YangMills
open YM YM.Spec YM.OPE YM.OPE.Orbits YM.Boundary
open scoped Classical
variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def hierarchy : Hierarchy (wilsonFamily C) where
  H := stateSpace F.action
  labels := labelsOf S
  theory := view F.action
  Field := S.Field
  toLabel := S.pin
  project := S.classTokens
  Character := F.α.space.X
  phaseMeasure := F.α.space.μ
  selected := F.α.atPoint
  correlation s v x := S.useAt (spectator F s) x v
  continuation v z x := F.A.waves.F _ z x (fun i => S.pin (v i).1 (v i).2)
  Channel := Q.channels
  channelField := Q.actor
  coefficient a j i x := Q.coef j i x (fun k => (a k).2)
  stress := F.sector.energy
  unitAtFour := S.unit 4

end YangMills
