import YM.Integration.WilsonIndependentMatchedOpeningFaithful
import YM.Integration.WilsonIndependentMatchedOpeningPayment
/-! The true filed public/survey stencil on its own tests is exactly its thermally priced finite family of genuine group stencils. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningFiled
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
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G){d D:ℕ}
local notation "F" => R.family.labels.level d

def planted (s:Bool)(w:d<D)(b:Volume D)(c:Verse F)(o:Cover):Era G ℝ:=
  shifted (tuftV (ContinuousLinearMap.apply ℝ ℝ b) (Shrine (plate (sectionAt R W s d) w) c)) o

def terms (s:Bool)(w:d<D)(b:Volume D)(c:Verse F)(o:Cover)(a:Alma F):Era G ℝ:=
  affiled (realDose R (w:=w) b c a) (column R W s w (seat F (sheet F a)) o)

theorem enrolled (s:Bool)(w:d<D)(b:Volume D)(c:Verse F)(o:Cover):Auth d (planted R W s w b c o):=by
  obtain ⟨_,_,book⟩:=WilsonIndependentMatchedFiledIncome.named R W s d w le_rfl 0 0
  exact ((On_auth (book c).1).tuft _).shifted _

theorem paid (s:Bool)(w:d<D)(b:Volume D)(c:Verse F)(o:Cover)(a:Alma F):
    Auth d (terms R W s w b c o a):=by
  exact (WilsonIndependentMatchedOpeningPayment.enrolled R W s w
    (seat F (sheet F a)) o (realDose R (w:=w) b c a)).tall (value_le F _)

theorem original (s:Bool)(w:d<D)(b:Volume D)(c:Verse F)(o:Cover):
    planted R W s w b c o=∑a,terms R W s w b c o a:=by
  have admit:=enrolled R W s w b c o
  have tickets:=paid R W s w b c o
  apply WilsonIndependentMatchedOpeningFaithful.original admit (Auth.sum (fun a _=>tickets a))
  intro n v
  have read:=WilsonIndependentMatchedOrdinarySeat.original R W s w b c o v
  change here n v (Blue.flash (skewV (wrap n o) (jot b ((Shrine _ c).1 n))))=_
  rw [read]
  have data:(∑a,terms R W s w b c o a).1 n=∑a,(terms R W s w b c o a).1 n:=by
    simp only [Prod.fst_sum,Finset.sum_apply]
  rw [data,flash_term _ (fun a _=>(tickets a).span n),map_sum]
  exact Finset.sum_congr rfl fun a _=>(WilsonIndependentMatchedOpeningPayment.value R W
    s w (seat F (sheet F a)) o (realDose R (w:=w) b c a) n v).symm
end YM.Integration.WilsonIndependentMatchedOpeningFiled
