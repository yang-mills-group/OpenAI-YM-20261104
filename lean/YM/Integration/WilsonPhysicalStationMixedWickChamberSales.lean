import YM.Integration.WilsonPhysicalStationMixedWickChamberPorts
import YM.Integration.WilsonPhysicalStationMixedWickPlacement
import YM.Integration.WilsonPhysicalStationOwnedMixedCourse

/-! A fixed generic lower reference and its actual original thermal election. -/
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickChamberSales
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
open WilsonMovingForkReporterFilament WilsonMovingForkReporterBraided
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent


open PhysicalNext.Repeat Lotus MergeProof PhysicalNext.Repeat.Legato Bandage Campaign
open Next.Foundations OPE Work.G08
open WilsonPhysicalStationBasisJury (Row Result)
open WilsonMovingForkReporterMeasuredRadii (observed)
open WilsonPhysicalStationBasisChronology (Bank)
open WilsonPhysicalStationOwnedTableNominations (size exhibit)
open WilsonPhysicalStationBasisJury (Menu)
open WilsonPhysicalStationOwnedMixedSchool (School)
open WilsonMovingForkReporterBothArms (Filed)
open WilsonMovingForkReporterBasisOnRun (Banks)
variable {G:Gauge}(R:Run G){T:Campaign R}(L:Pillars R T){f:Extraction.Order}{S:Table R.family.book}
    (fac:Facilities R.family f S)(F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}
    (J₀:ℝ→tower S)(H:(Bel R.family.book).Hierarchy){arch:Arch R.family}
    {height:ℕ}{slots:Fin height→ℕ}(rows:(i:Fin height)→Fin (slots i)→Row R.family (i.val+1))
    (needs:∀d:ℕ,(ℝ→Fin 3→Tapes.Panel d)→ℝ→ℕ)

open MS MS.Land MS.Menus MS.Theater XSpace.Structure1
open Local.Physical
open WilsonMovingForkReporterMixedBasis (Slot)
open WilsonPhysicalStationMixedWickSolvent (Room)
open WilsonPhysicalStationMixedWickCollege (chosen)
open WilsonPhysicalStationMixedWickNamedGram (electrode)
open WilsonPhysicalStationOwnedMixedCourse (Grant)

variable (book:Deck G)(lo hi:ℕ→ℕ)(ax:ℕ→Axis)
open WilsonPhysicalStationMixedWickChamberPorts (grade quantity contact ledger booked)
open WilsonMovingForkReporterMixedHouses (Held)
open WilsonPhysicalStationMixedBasisSale (Sold)
variable (counted:ℕ→ℕ)(more:∀d,Fin (counted d)→Slot R.family)
    (bind:Binding R.family)(O:HaarBudget G)(χ:ChartRatio G)(price:ℕ→ℝ)
    {D m:ℕ}(P:Tapes.Panel D)(V:Vane R.family m)(check:V.checked f H m)
    (held:Held (f:=f) R bind O χ H price (quantity R lo hi counted)
      (ledger R (S:=S) book lo hi ax counted more) P V)

include held in
theorem original (i:Fin (D+1))(l r:Bool)(b:(R.family.labels.level (grade (lo i) (hi i) r)).Index)
    (s:Signed)(v:Fin 2)(hl:grade (lo i) (hi i) l < m+1)(hr:grade (lo i) (hi i) r < m+1)
    (width:100*(max (grade (lo i) (hi i) l) (grade (lo i) (hi i) r)+1)≤D):
    Sold R V (contact R (S:=S) book lo hi ax i l r b s v) hl hr D check:=
  WilsonPhysicalStationMixedWickPlacement.occupied R bind O χ price P V check held _
    (booked R (S:=S) book lo hi ax counted more D i l r b s v) hl hr width

include held in
theorem basis (i:Fin (D+1))(he:lo i < m+1)(width:100*(lo i+1)≤D)
    (b:(R.family.labels.level (lo i)).Index):
    let room:=chosen R (S:=S) book (lo i) (ax i)
    Sold R V (electrode R (lo i) room.site room.compact room.clear b) he he D check:=
  original R (H:=H) book lo hi ax counted more bind O χ price P V check held i false false b 1 0 he he
    (by simpa only [WilsonPhysicalStationMixedWickChamberPorts.grade,max_self] using width)

end YM.Integration.WilsonPhysicalStationMixedWickChamberSales
end
