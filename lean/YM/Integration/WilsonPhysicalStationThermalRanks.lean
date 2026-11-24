import YM.Integration.WilsonPhysicalThermalWickProbe
import YM.Integration.WilsonPhysicalThermalWickRankBound
import YM.Integration.WilsonPhysicalThermalWickSky

/-! The two counted source arguments on the actual reflected panel,
before choosing either cutoff and before taking the real heating inverse. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationThermalRanks
open Lattice Wilson RG Source Cells Extraction Table
open Further.CorrectedLift (ladder)
open WilsonPhysicalPositionReflectedReturn (ports)
open WilsonPhysicalThermalWickRankSupport (Counted)
open WilsonPhysicalThermalWickRescale (pure)
open WilsonPhysicalThermalWickSky (labels)
open Next.Rank.Configuration
open scoped BigOperators Classical
variable {G:Gauge}(C:Family G){d h:ℕ}
local notation "F"=>C.labels.level d

def probe (b:(C.labels.level d).Index)(s:Signed)(i:Fin 2): (standard C).Field d:=
  ports (C:=C) ((standard C).project d (Pi.single b 1)) s i

def fields (x:C.label d)(z:(standard C).Field d):Fin 2→C.label d:= ![x,ladder C d z]

theorem counted (x:C.label d)(z:(standard C).Field d)(r Q:ℕ)(lo:Counted F x r)
    (hi:Counted F (ladder C d z) Q)(cap:d≤h)(i:Fin 2):
    pure (![r,Q] i) (thawKey (labels (d0:=fun _:Fin 2=>d) (fields C x z) (fun _=>cap) i)):=by
  fin_cases i
  · exact WilsonPhysicalThermalWickRankSupport.polynomial F x r lo cap
  · exact WilsonPhysicalThermalWickRankSupport.polynomial F _ Q hi cap

theorem original (a b:(C.labels.level d).Index)(s:Signed)(e:Fin 2)(cap:d≤h):
    let v:=fields C (Pi.single a 1) (probe C b s e)
    let q:Fin 2→ℕ:=![(C.labels.level d).grades a |>.2,(C.labels.level d).grades b |>.2]
    (∀i,pure (q i) (thawKey (labels (d0:=fun _:Fin 2=>d) v (fun _=>cap) i))) ∧ ∀i,q i≤h:=by
  dsimp only
  constructor
  · exact counted C _ _ _ _ (WilsonPhysicalThermalWickRankSupport.axis F a)
      (WilsonPhysicalThermalWickProbe.original C b s e) cap
  · intro i
    fin_cases i
    · exact (WilsonPhysicalThermalWickRankBound.original F a).trans cap
    · exact (WilsonPhysicalThermalWickRankBound.original F b).trans cap

end YM.Integration.WilsonPhysicalStationThermalRanks
end
