import YM.Integration.WilsonIndependentMatchedOpeningRoster
import YM.Integration.WilsonIndependentMatchedOpeningColumn
/-! Filed arbitrary finite thermal doses applied at the actual translated K pupil. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningPayment
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
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G){d D:ℕ}
local notation "F" => R.family.labels.level d

def affiled (cash:Blue.Cost)(M:Era G ℝ):Era G ℝ:=(fun n=>affix cash (M.1 n),affix cash M.2)
theorem carried {U α:Type}[AddGroup U](o:U)(b:Volume D)(q:Blue.Cost)(Y:Pal (Vote D) (U×α)):
    skewV o (jot b (affix q Y))=affix q (skewV o (jot b Y)):=by
  rw [jotAffix]
  funext e r x
  simp [skewV,revolve,affix,Finset.sum_apply]

theorem enrolled (s:Bool)(w:d<D)(a:Alma F)(o:Cover)(q:Blue.Cost):
    Auth (valence F a) (affiled q (column R W s w a o)):=by
  obtain ⟨live,_⟩:=WilsonIndependentMatchedSectionIncome.named R W s d w a le_rfl 0 0
  let Y:=leaf (sectionAt R W s d) w a
  let b:=brow F a D
  have image:=((On_auth (live.stem q)).tuft (ContinuousLinearMap.apply ℝ ℝ b)).shifted o
  convert image using 1
  apply Prod.ext
  · funext n
    exact (carried (wrap n o) b q (Y.1 n)).symm
  · exact (carried o b q Y.2).symm

theorem value (s:Bool)(w:d<D)(a:Alma F)(o:Cover)(q:Blue.Cost)(n:Side)(y:TreeVars G n):
    here n y (Blue.flash ((affiled q (column R W s w a o)).1 n))=
      q * RegulatorIR.Halo.shelter (valence F a)
        (WilsonIndependentRawNamedStencil.shifted R W s d (sheet F a) o)
        (sample y):=by
  have live:=WilsonIndependentMatchedOpeningColumn.enrolled R W s w a o
  change here n y (Blue.flash (affix q _))=_
  rw [sponsor _ _ (live.span n),map_mul,WilsonIndependentMatchedOrdinarySeat.ground,
    WilsonIndependentMatchedOpeningColumn.ray R W s w a o n y]
end YM.Integration.WilsonIndependentMatchedOpeningPayment
