import YM.Integration.WilsonPhysicalThermalWickRankSupport
import YM.Integration.WilsonPhysicalStationThermalPair
import YM.Integration.WilsonPhysicalPositionReflectedReturn

/-! Verify field count on the actual reflected physical lift. The free
null complement belongs to the original section at its prescribed
grade and is retained by the incoming thermal inverse. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickProbe
open Lattice Wilson RG Labels Function Cells Source Extraction Table Maxwell Maxwell.Free
open Further.CorrectedLift Push.CutoffProjectors
open WilsonPhysicalThermalWickRankSupport (Counted)
open WilsonPhysicalPositionReflectedReturn (ports)
open scoped BigOperators Classical
variable {G:Gauge}(C:Family G){d:ℕ}
local notation "F"=>C.labels.level d

theorem projected (x:C.label d)(q:ℕ)(count:Counted F x q):
    Counted F (ladder C d ((standard C).project d x)) q:=by
  rw [ladder_on]
  intro t
  have commute:retain F ((standard C).null d) ((C.labels.level d).scaled t x)=
      (C.labels.level d).scaled t (retain F ((standard C).null d) x):=free_scaled C t x
  rw [←commute,count t,map_smul]

theorem mirrored (w:(standard C).Field d)(q:ℕ)(count:Counted F (ladder C d w) q)(a:Signed):
    Counted F (ladder C d ((standard C).mirror (spin_free C.labels) d a w)) q:=by
  rw [ladder_spin]
  intro t
  change (C.labels.level d).scaled t ((C.labels.level d).act (Signed.inclusionO a) _) = _
  rw [(C.labels.level d).scaling,count t,map_smul]

theorem conjugated (w:(standard C).Field d)(q:ℕ)(count:Counted F (ladder C d w) q):
    Counted F (ladder C d ((standard C).conj (spin_free C.labels) d w)) q:=by
  rw [ladder_conj]
  intro t
  funext i
  have e:=congrArg star (congrFun (count t) i)
  simpa only [Frame.scaled_apply,Pi.smul_apply,Pi.star_apply,smul_eq_mul,star_mul',Complex.star_def,
    Complex.conj_ofReal,mul_comm] using e

theorem original (j:(C.labels.level d).Index)(a:Signed)(i:Fin 2):
    Counted F (ladder C d (ports (C:=C) ((standard C).project d (Pi.single j 1)) a i)) ((C.labels.level d).grades j).2:=by
  let v:=(standard C).project d (Pi.single j 1)
  have filed:Counted F (ladder C d v) ((C.labels.level d).grades j).2:=
    projected C _ _ (WilsonPhysicalThermalWickRankSupport.axis F j)
  have seen:=mirrored C v _ filed a
  fin_cases i
  · exact seen
  · exact mirrored C _ _ (conjugated C _ _ seen) (Signed.mirror 0)

end YM.Integration.WilsonPhysicalThermalWickProbe
end
