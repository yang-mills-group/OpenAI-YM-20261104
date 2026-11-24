import YM.Integration.WilsonThermometerUnitFilingCoverBasis
import YM.Integration.WilsonThermometerUnitFilingCoverEra

/-! The actual group word at a translated birth, on the original restricted quiet history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingPinBirth
open Function Lattice Wilson RG Gauge RegulatorIR Geometry Taping Budget Budget.Packet Budget.Tuple
open Diagram Prim Profiles Halo Ledger Ledger.Sky Cluster Uniform
open WilsonThermometerUnitFilingCoverStock
open scoped ENNReal Classical BigOperators
variable {G:Gauge}{W:Type}{M:W→ℕ}{n:Page M→Side}{S:Heir n G}(T:S.Accounts)
  {h:ℕ}(F:W→Portrait G)(law:∀v,LocalStamp (F v) h)(v:W)(z:W → Cover)

def located (s:W):Portrait G:=convey (z s) (F s)
include law in
theorem lawful (s:W):LocalStamp (located F z s) h:=(law s).moves
theorem field (s:W)(t:ℝ)(U:CoverConfig G):located F z s t U=F s t (translate (z s) U):=rfl

theorem original :
    (report T (located F z) (lawful F law z)).main (Page.opening M v)=
      fun e r=>echo (carryX (z v)) ((report T F law).main (Page.opening M v) e r):=by
  let q:= (report T F law).main (Page.opening M v)
  have left:=opening T (located F z) (lawful F law z) v
  have right:=opening T F law v
  apply certifies left.1 (right.1.vayne (z v))
  · rw [left.2]
    exact (stamp_symbol ((lawful F law z) v)).choose_spec.2
  · intro e r nz
    have ranks:Ranks h q:=by
      change Ranks h ((report T F law).main (Page.opening M v))
      rw [right.2]
      exact (stamp_symbol (law v)).choose_spec.2
    apply ranks e r
    intro hz
    apply nz
    change echo _ (q e r)=0
    rw [hz,echo_zero]

theorem scalar (e:ℕ)(r0:Tuple (Foot G) 0):
    (report T (located F z) (lawful F law z)).main (Page.opening M v) e 0 r0=
      (report T F law).main (Page.opening M v) e 0 r0:=by
  rw [original T F law v z]
  exact congrArg ((report T F law).main (Page.opening M v) e 0) (Subsingleton.elim ..)

end YM.Integration.WilsonThermometerUnitFilingPinBirth
