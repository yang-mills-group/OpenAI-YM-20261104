import YM.Integration.WilsonIndependentConditionedFolioVisit
import YM.Integration.WilsonIndependentConditionedFolioVolume
import YM.Integration.WilsonSeparatedPrefixMovingFixedCapture
import YM.Integration.WilsonOriginalPublicNodalTestedChronology

/-! An individual native visit of the tested pupil on every occupied mark. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedFolioInventory
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

open WilsonIndependentRawRosterWord (fold degree)
open RegulatorIR.Cluster (Composite)
open WilsonIndependentMatchedOpeningRoster (field)
open WilsonIndependentRawPhysicalFaces (ordered entered)
open WilsonOriginalPublicNodalTestedChronology (registered rank)
open WilsonIndependentConditionedFolioPupil (atSite)

open WilsonIndependentMatchedOpeningRoster (enrolled)
open WilsonIndependentRawPhysicalFaces (Lists)
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I][Nonempty I](R:Run G)(W:Initialize G)
  (σ:I→Bool)(d:I→ℕ)(key:∀i,(R.family.labels.level (d i)).Index){D:I→ℕ}(cut:∀i,d i<D i)(o:I → Cover)

private def sight (n:Side)(v:TreeVars G n)(X:Era G ℝ):Cost:=here n v (Blue.flash (X.1 n))

omit [Fintype I] [DecidableEq I] [Nonempty I] in
private theorem ray (n:Side)(v:TreeVars G n)(J:Composite I):
    sight n v (field R W σ d key cut o J)=fold (fun i=>sight n v
      (column R W (σ i) (cut i) (seat (R.family.labels.level (d i)) (key i)) (o i))) J:=by
  induction J with
  | atom=>rfl
  | pair A B ihA ihB=>
    rw [WilsonIndependentRawRosterWord.fold,←ihA,←ihB]
    exact (congrArg (here n v) (woadap _ _ (finite_shell ((enrolled R W σ d key cut o A).span n))
      (finite_shell ((enrolled R W σ d key cut o B).span n)))).trans (map_mul (here n v) _ _)

local instance full_nonempty (ι:Type)[Fintype ι][Nonempty ι]:Nonempty (↥(Finset.univ:Finset ι)):=
  ⟨⟨Classical.arbitrary ι,Finset.mem_univ _⟩⟩

omit [DecidableEq I] in
theorem filed (J:Composite I)(all:Lists Finset.univ J):
    field R W σ d key cut o J=field R W (fun i:(Finset.univ:Finset I)=>σ i) (fun i=>d i) (fun i=>key i)
      (fun i=>cut i) (fun i=>o i) ordered:=by
  classical
  let s:=Finset.univ (α:=I)
  letI :Nonempty s:=full_nonempty I
  have p:=enrolled R W σ d key cut o J
  have q:=enrolled R W (fun i:s=>σ i) (fun i=>d i) (fun i=>key i) (fun i=>cut i) (fun i=>o i) ordered
  apply WilsonIndependentMatchedOpeningFaithful.original (p.tall (Nat.le_add_right _ _)) (q.tall (Nat.le_add_left _ _))
  intro n v
  change sight n v _=sight n v _
  rw [ray,ray,all.product,entered.product]
  rw [←Finset.prod_coe_sort (Finset.univ:Finset I)]

theorem pair (d:Fin 2→ℕ)(key:∀i,(R.family.labels.level (d i)).Index){D:Fin 2→ℕ}
    (cut:∀i,d i<D i)(o:Fin 2 → Cover):
    agateV (column R W false (cut 0) (seat (R.family.labels.level (d 0)) (key 0)) (o 0))
      (column R W false (cut 1) (seat (R.family.labels.level (d 1)) (key 1)) (o 1))=
      registered R W d key cut o (Finset.univ:Finset (Fin 2)):=by
  classical
  apply filed R W (fun _:Fin 2=>false) d key cut o (.pair (.atom 0) (.atom 1))
  constructor
  · intro A inst f
    simp only [WilsonIndependentRawRosterWord.fold,Fin.prod_univ_two]
  · intro x site
    simp only [WilsonIndependentRawRosterBudget.span,Fin.sum_univ_two]

end YM.Integration.WilsonIndependentConditionedFolioInventory
end
