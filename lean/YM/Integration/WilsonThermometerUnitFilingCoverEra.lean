import YM.Integration.WilsonThermometerUnitFilingCoverStock
import YM.RegulatorIR.Ledger.Turn

/-! Start the captured one-name source on a genuine suffix of the original quiet history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverEra
open Function Lattice RegulatorIR Budget Spatial Budget.Packet Uniform Diagram Ledger Ledger.Sky
open Taping Profiles Prim Halo WilsonThermometerUnitFilingCoverStock
variable {G:Gauge} {W:Type} {M:W→ℕ} {n:Page M→Side} (S:Heir n G) (T:S.Accounts)
  {L:Meter W}{p b h:ℕ}(P:S.Primitive L p b)(k:Choice M)
  (B:W→Portrait G)(law:∀ w,LocalStamp (B w) h)
local notation "dates"=>k.after
local notation "older"=>k.after.expanse S
local notation "vacuum"=>k.after.part S T P

def filed:(vacuum).Report h:=WilsonThermometerUnitFilingCoverStock.report (S:=older) (vacuum) B law

theorem origin (w:W):BasisT h h (B w)
    ((filed S T P k B law).main (Page.opening k.after.spans w)) ∧
    (vacuum).bulk (Page.opening k.after.spans w)=T.bulk (k.choose w) ∧
    (vacuum).orb (Page.opening k.after.spans w)=T.orb (k.choose w):=
  ⟨(opening (S:=older) (vacuum) B law w).1,rfl,rfl⟩

theorem joined (w:Flap k.after.spans):
    let Z:=filed S T P k B law
    (S.frames (k.after.wing w)).each h (T.bulk (k.after.page w.prev)) (Z.main w.prev)=Z.main w.next ∧
    (S.frames (k.after.wing w)).island h (T.orb (k.after.page w.prev)) (Z.point w.prev)=Z.point w.next:=
  ⟨(filed S T P k B law).step_m w,(filed S T P k B law).step_p w⟩

end YM.Integration.WilsonThermometerUnitFilingCoverEra
