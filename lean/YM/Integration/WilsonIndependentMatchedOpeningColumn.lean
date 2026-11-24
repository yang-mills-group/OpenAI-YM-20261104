import YM.Integration.WilsonIndependentMatchedOrdinarySeat
import YM.Integration.WilsonIndependentMatchedSectionIncome
import YM.Integration.WilsonIndependentSpoutAtomicPolar

/-! The unweighted named opening is the same finite group field, read at its genuine dual test. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningColumn
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
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G){d D:ℕ}
local notation "F" => R.family.labels.level d

def column (survey:Bool)(w:d<D)(a:Alma F)(o:Cover):Era G ℝ:=
  shifted (tuftV (ContinuousLinearMap.apply ℝ ℝ (brow F a D)) (leaf (sectionAt R W survey d) w a)) o

theorem enrolled (survey:Bool)(w:d<D)(a:Alma F)(o:Cover):
    Auth (valence F a) (column R W survey w a o):=by
  obtain ⟨paid,_⟩:=WilsonIndependentMatchedSectionIncome.named R W survey d w a le_rfl 0 0
  exact ((On_auth paid).tuft _).shifted _

private theorem single (survey:Bool)(w:d<D)(a:Alma F):
    Shrine (plate (sectionAt R W survey d) w) (Pi.single a 1)=leaf (sectionAt R W survey d) w a:=by
  unfold Shrine
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _),Pi.single_eq_same]
  · exact Prod.ext (funext fun n=>affix_plain _) (affix_plain _)
  · intro b _ diff
    rw [Pi.single_eq_of_ne diff]
    exact Prod.ext (funext fun n=>no_tariff _) (no_tariff _)

theorem ray (survey:Bool)(w:d<D)(a:Alma F)(o:Cover)(n:Side)(v:TreeVars G n):
    here n v (flash ((column R W survey w a o).1 n))=
      RegulatorIR.Halo.shelter (valence F a) (WilsonIndependentRawNamedStencil.shifted R W survey d (sheet F a) o) (sample v):=by
  have ht:=WilsonIndependentMatchedOrdinarySeat.original R W survey w (brow F a D) (Pi.single a 1) o v
  rw [single] at ht
  change here n v (flash (skewV (wrap n o) (jot (brow F a D) ((leaf (sectionAt R W survey d) w a).1 n))))=_
  rw [ht,received,Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
  · simp [WilsonIndependentMatchedTopReceipt.realDose,packBloom]
  · intro b _ diff
    simp [WilsonIndependentMatchedTopReceipt.realDose,Pi.single_eq_of_ne diff]

end YM.Integration.WilsonIndependentMatchedOpeningColumn
