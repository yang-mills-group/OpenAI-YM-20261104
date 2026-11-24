import YM.Integration.WilsonIndependentNotebookConstantSeat
import YM.Integration.WilsonIndependentMatchedOpeningFiled

/-! The conditioned constant public dose on a genuine, located compact pupil. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedFolioIssue
open Function Filter Finset PowerSeries Lattice RG Wilson Tree Source Labels
open Laurent Bloch Metric FreeResolvent Work.F08 Precision Exterior Gauge XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Bank
open WilsonCoeffUV.Wheel.Flooring PertExtension RegulatorIR RegulatorIR.Budget
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedSectionIncome (leaf)
open WilsonIndependentMatchedOrdinarySeat (here received)
open WilsonIndependentSpoutOrdinaryPlate (sample)
open scoped Classical BigOperators
open WilsonIndependentMatchedTopReceipt (realDose)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOpeningRoster (seat)
open WilsonIndependentMatchedOpeningPayment (affiled)

open WilsonIndependentNotebookConstantSeat (issue part)
open private seated_sum from YM.Integration.WilsonIndependentNotebookConstantSeat
open WilsonIndependentMatchedOpeningRoster (seat)
open WilsonIndependentMatchedOpeningFiled (planted)
open WilsonIndependentMatchedOpeningColumn (column)

private theorem paid {G:Gauge}(q:ℝ)(P:Era G ℝ):affiled (C q) P=q•P:=by
  apply Prod.ext
  · exact funext fun n=>purePayment _ q
  · exact purePayment _ q

variable {G:Gauge}(R:Run G)(W:Initialize G){d D:ℕ}(w:d<D)
local notation "F" => R.family.labels.level d

theorem original (b:Volume D)(im:Bool)(z:(R.family.labels.level d).Index→ℂ)(o:Cover):
    planted R W false w b (issue F im z) o=
      ∑i:(R.family.labels.level d).Index,(part im (z i)*jewelBloom w (seat F i) b)•column R W false w (seat F i) o:=by
  classical
  rw [WilsonIndependentMatchedOpeningFiled.original]
  rw [seated_sum («F»:=F) _ (fun a empty=>by
    change affiled (issue F im z a*C ((jewelBloom w a) b)) _=0
    rw [show issue F im z a=0 from if_neg empty,zero_mul,←map_zero (C (R:=ℝ)),paid,zero_smul])]
  apply Finset.sum_congr rfl
  intro i _
  change affiled (issue F im z (WilsonIndependentNotebookConstantSeat.seat F i)*C ((jewelBloom w (seat F i)) b))
    (column R W false w (seat F i) o)=_
  rw [WilsonIndependentNotebookConstantSeat.seated,←map_mul,paid]

end YM.Integration.WilsonIndependentConditionedFolioIssue
end
