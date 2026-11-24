import YM.Integration.WilsonIndependentConditionedFolioIssue
import YM.Integration.WilsonIndependentMatchedCoverProfile

/-! The full affine Mer pupil on its actual named mesh and common translation. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedFolioPupil
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


open WilsonIndependentMatchedCoverProfile (word)
variable {G:Gauge}(R:Run G)(W:Initialize G){d D:ℕ}(w:d<D)
local notation "F" => R.family.labels.level d

theorem atSite (i:(R.family.labels.level d).Index)(φ:Rarity D)(x y:ℝ)(o:CellR)(n:Cover):
    jewelBloom w (seat F i) (wheelC x y n φ.ψ o)=φ.ψ.val (Mer.position x y o n):=by
  change iteratedFDeriv ℝ 0 (fun v:Point4=>φ.ψ.val (Mer.address x y o n v)) (zeroC:Point4) (dot ∘ knurl (notar F (seat F i)))=_
  rw [iteratedFDeriv_zero_apply]
  simp [Mer.address,zeroC]

theorem original (im:Bool)(a:(R.family.labels.level d).Index→ℂ)(φ:Rarity D)(x y:ℝ)(o:CellR)(h:ℕ):
    word (Shrine (plate (sectionAt R W false d) w) (issue F im a)) φ x y o h=
      ∑n∈canvasM φ x y,drumB h x •
        ∑i:(R.family.labels.level d).Index,(part im (a i)*φ.ψ.val (Mer.position x y o n)) •
          column R W false w (seat F i) n:=by
  classical
  unfold word pupil
  rw [shoreSum]
  apply Finset.sum_congr rfl
  intro n _
  apply congrArg (fun Z:Era G ℝ=>drumB h x • Z)
  change planted R W false w (wheelC x y n φ.ψ o) (issue F im a) n=_
  rw [WilsonIndependentConditionedFolioIssue.original]
  simp only [atSite]

end YM.Integration.WilsonIndependentConditionedFolioPupil
end
