import YM.Integration.WilsonPhysicalStationMixedWickTest
import YM.Integration.WilsonMeasuredPublicEntranceThermalRankPair
/-! The exact foreign Wick ranks at different engineering heights on the prescribed physical ports. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedForeign
open Lattice Wilson RG Source Cells Extraction Table Extra.FD Maxwell Maxwell.Wick
open scoped Classical BigOperators
variable {G:Gauge}(C:Family G){d:ℕ}
local notation "F" => C.labels.level d
local notation "T" => standard C

open WilsonPhysicalStationMixedWickTest (reference fields)
open WilsonOriginalBlissMixedGram (grades)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonMeasuredPublicEntranceThermalRankPair (axis submitted)
variable {r:ℕ}
theorem original (a:(F).Index)(b:(C.labels.level r).Index)(s:Signed)(side:Fin 2)(x:Points 2)
    (apart:((F).grades a).2≠((C.labels.level r).grades b).2):
    reference C (Pi.single a 1) (probe C b s side) x=0:=by
  let v:=probe C b s side
  let y:=fields C (Pi.single a (1:ℂ)) v
  have right:Length (writes C.labels r v) ((C.labels.level r).grades b).2:=by
    have actual:=submitted C (Further.CorrectedLift.ladder C r v) _ (WilsonPhysicalThermalWickProbe.original C b s side)
    rwa [Further.CorrectedLift.ladder_reads] at actual
  change (T).useAt T x (fun i=>⟨grades d r i,y i⟩)=0
  rw [writes_eval]
  change moment G x (fun i=>writes C.labels (grades d r i) (y i))=0
  rw [show (fun i=>writes C.labels (grades d r i) (y i))=
    ![writes C.labels d ((T).project d (Pi.single a 1)),writes C.labels r v] from
    funext (fun i=>by fin_cases i <;> rfl)]
  exact FVAAlt2.Home.Report.stepNone _ _ x (axis C a) right apart

end YM.Integration.WilsonPhysicalStationMixedForeign
end
