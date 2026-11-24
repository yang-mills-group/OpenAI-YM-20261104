import YM.Integration.WilsonMeasuredSignedActionDirection
import YM.Integration.WilsonMeasuredPublicEntranceActionPremium
import YM.Pert.Scale.Return

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonMeasuredSignedActionEngineering
open Labels Trace Trace.Pilot Pert Pert.RawLabels
variable {G:Gauge}(C:Family G)

theorem weight : (square4 G).val.IsWeightedHomogeneous generation 4:=by
  have graded:(square4 G).val.IsWeightedHomogeneous bidegree (4,2):=
    WilsonMeasuredPublicEntranceActionPremium.grade
  intro u h
  have pair:Finsupp.weight bidegree u=(4,2):=by
    exact graded h
  rw [weight_slot] at pair
  have he:=congrArg Prod.fst pair
  simpa [height,Finsupp.weight_apply,Finsupp.sum] using he

theorem original (t:ℝ):
    Pert.Scale.gear C.labels 4 t (stepField C)=(t:ℂ)^4 • stepField C:=by
  change Pert.Scale.gear C.labels 4 t (enroll C.labels 4 (square4 G))=_
  rw [Pert.Scale.gear_inherit,Pert.Scale.grow_weights (p:=square4 G) weight t,map_smul]
  rfl

end YM.Integration.WilsonMeasuredSignedActionEngineering
end
