import YM.Integration.WilsonMaxwellThermometerSurveyThreeRoster
import YM.Integration.WilsonMaxwellThermometerSurveyAtlas

/-! Every occupied or deleted horizon/axis combination in the calibrated
two-source wallet is an actual W-registry insertion on its own sites. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerSurveyThreePins
open Function Finset XSpace XSpace.Cirrus Wilson PhysicalNext.Repeat.Legato Lattice
open WilsonThermometerPositionTunedPublicCharge (Picked)
open WilsonMaxwellThermometerSurveyThreeRoster (Pin read printedPin)
open private printed from YM.Integration.WilsonMaxwellThermometerSurveyThreeRoster
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G)

def slots (v:Pin R):Finset (Fin 3):=univ.filter fun j=>(v j).isSome
def pick (v:Pin R):Picked R 6 (slots R v):=fun j=>(v j).get (Finset.mem_filter.mp j.property).2

theorem stamped (v:Pin R):printedPin R (slots R v) (pick R v)=v:=by
  funext j
  cases eq:v j with
  | none => simp [printedPin,slots,eq]
  | some u =>
    have live:j∈slots R v:=by simp [slots,eq]
    rw [printedPin,dif_pos live]
    exact (Option.some_get (Finset.mem_filter.mp live).2).trans eq

def heights (v:Pin R)(j:slots R v):ℕ:=(pick R v j).1
def columns (v:Pin R)(j:slots R v):(R.family.labels.level (heights R v j)).Index:=(pick R v j).2

theorem placed (W:Initialize G)(t:Sample 3)(v:Pin R):
    read R W t v=WilsonThermometerPositionTunedCorrection.surveyed R W (heights R v) t.F.p
       (t.layout ∘ Subtype.val) (W.tree t.F.p) (columns R v):=by
  calc
    _ = read R W t (printedPin R (slots R v) (pick R v)):=congrArg (read R W t) (stamped R v).symm
    _ = _:=printed R W t (slots R v) (pick R v)
end YM.Integration.WilsonMaxwellThermometerSurveyThreePins
end
