import YM.Integration.WilsonMovingForkSharpTested44
import YM.Integration.WilsonIndependentMatchedElectedOrbit
import YM.Integration.WilsonMaxwellThermometerSurveyIncome
import YM.Integration.WilsonIndependentMatchedNamedPair

/-! Common public section for the elected Mer product and the named finite Wilson insertions. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpSections
open Function Filter Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonLimitConstruction Labels Source Source.Drops XSpace
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMatchedElectedOrbit (chosen filed)
open WilsonIndependentMatchedNamedPair (sectionAt)
open scoped Classical

def publicFrame {G:Gauge}(R:Run G):Master (hol G) where
  F:=R.family.labels.level
  T:=R.family.localSection
  spec h:=(congrArg (fun H=>(R.family.localSection h).Sound H)
    (WilsonEpochPositionCoefficients.holonomy R.family.params (hol G))).mp (R.makes.sections h)
  pop h:=FVAAlt2.Block.clothes R h

theorem section_eq {G:Gauge}(R:Run G)(W:Initialize G)(d:ℕ):
    (publicFrame R).T d=sectionAt R W false d:=rfl

theorem print_eq {G:Gauge}(R:Run G)(W:Initialize G)(d:ℕ)(a:(R.family.labels.level d).Index)(o:Cover):
    (chosen (publicFrame R) d a o).print=(filed R W false d a o).print:=rfl

theorem group_eq {G:Gauge}(R:Run G)(W:Initialize G)(d:ℕ)(a:(R.family.labels.level d).Index)
    (o:Cover)(n:Side):
    (chosen (publicFrame R) d a o).group n=(filed R W false d a o).group n:=rfl

end YM.Integration.WilsonMovingForkSharpSections
