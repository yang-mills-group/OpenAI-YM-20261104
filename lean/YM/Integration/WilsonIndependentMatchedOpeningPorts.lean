import YM.Integration.WilsonIndependentMatchedOpeningAccrued
/-! Genuine visited sites and all enrolled basis directions at their individual angular grades. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningPorts
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
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedOpeningFiled (terms planted)
open WilsonIndependentMatchedOpeningAccrued (group)
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G){d D:ℕ}
local notation "F" => R.family.labels.level d
abbrev Port (B:Labels.Frame G d)(φ:Rarity D)(x y:ℝ)(o:CellR):=
  (↑(VisitsT φ x y o)) × Alma B

def submitted (s:Bool)(w:d<D)(c:Verse F)(φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ)(u:Port F φ x y o):Era G ℝ:=
  drumB l x • terms R W s w (wheelC x y u.1.val φ.ψ o) c u.1.val u.2

theorem paid (s:Bool)(w:d<D)(c:Verse F)(φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ)(u:Port F φ x y o):
    Auth (valence F u.2) (submitted R W s w c φ x y o l u):=by
  exact (WilsonIndependentMatchedOpeningPayment.enrolled R W s w (seat F (sheet F u.2)) u.1.val
    (realDose R (w:=w) (wheelC x y u.1.val φ.ψ o) c u.2)).μ _

theorem grouped (s:Bool)(w:d<D)(c:Verse F)(φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ):
    group R W s w c φ x y o l=∑u:Port F φ x y o,submitted R W s w c φ x y o l u:=by
  rw [Fintype.sum_prod_type]
  change (∑z∈VisitsT φ x y o,drumB l x • ∑j,terms R W s w (wheelC x y z φ.ψ o) c z j)=_
  rw [←Finset.sum_coe_sort (VisitsT φ x y o)]
  apply Finset.sum_congr rfl
  intro z _
  simp only [submitted,Finset.smul_sum]
end YM.Integration.WilsonIndependentMatchedOpeningPorts
