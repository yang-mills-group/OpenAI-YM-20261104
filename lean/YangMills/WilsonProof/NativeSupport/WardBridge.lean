import YangMills.StressTensor
import YangMills.WilsonProof.NativeSupport.YangMills.CorrelationHierarchy
import YangMills.WilsonProof.NativeSupport.HierarchySpec
import YangMills.WilsonProof.NativeSupport.HierarchyBridge

/-! The shell laws, field rotations and derivatives on each public correlation
function are the laws of the original Wilson hierarchy and of each of its phases. -/
set_option autoImplicit false
noncomputable section
namespace YangMills
open YM YM.Spec YM.OPE YM.OPE.Orbits
open scoped Matrix.Norms.Frobenius

variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

private theorem phaseWard (s : Viewers F) :
    Table.StressLaws (spectator F s) F.sector.energy F.sector.derivatives.deriv F.sector.turns.lie := by
  cases s with
  | none => exact F.phase.transport.charges
  | some i => exact F.phase.phase.flux i

def publicWards : (hierarchy F Q).StressWardLaws where
  derivative := F.sector.derivatives.deriv
  derivativeInsertion s d a v {n} x hx q := (spectate_evolution F s).kernels d a v hx q
  act := F.sector.turns.act
  identity := F.phase.transport.spots.fixes
  composition := F.phase.transport.spots.group
  continuous := F.phase.transport.spots.spin
  covariance s n v x hx R := by
    cases s with
    | none => exact F.phase.transport.motion n v x hx R
    | some i => exact F.phase.phase.sym i n v x hx R
  generator d A := F.sector.turns.lie d ⟨A.val, A.property⟩
  infinitesimal d A v := F.phase.transport.spots.infinitesimal d ⟨A.val, A.property⟩ v
  symmetric := F.phase.transport.conserved.symmetric
  divergence := F.phase.transport.conserved.divergence
  tensor := F.phase.transport.spin
  translation s {n d} x hx v q χ window b :=
    ((phaseWard F s).translation hx q window b d v).trans ((spectate_evolution F s).kernels d b v hx q)
  rotation s {n d} x hx v q χ window A :=
    (phaseWard F s).rotation hx q window ⟨A.val, A.property⟩ d v

end YangMills
