import YM.Integration.WilsonPhysicalStationMixedWickSolvent
import YM.Integration.WilsonPhysicalStationMixedWickPlacement
import YM.Integration.WilsonPhysicalStationOwnedMixedCourse

/-! A fixed generic lower reference and its actual original thermal election. -/
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickCollege
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
open WilsonPhysicalStationMixedWickPlacement (menu quantity)
open WilsonPhysicalStationOwnedMixedCourse (Grant)
variable (book:Deck G)(e:ℕ)(a:Axis)

def chosen : Room R (S:=S) book e a:=
  Classical.choice (WilsonPhysicalStationMixedWickSolvent.original R book e a)

include L fac in
theorem original {n:ℕ}(extra:Fin n→Slot R.family)(hg:G.Simple)
    (roofs:R2I.RG05Joint.ReporterRoofs.Roofed R.kit)
    (lead:Leading F J₀)(bliss:Bliss F l arch H)(below:(l:Filter _)≤f.fuse):
    let room:=chosen R (S:=S) book e a
    Grant R F (l:=l) J₀ H (arch:=arch) rows needs (quantity R e n)
      (menu R e room.site room.compact room.clear extra) hg:=by
  let room:=chosen R (S:=S) book e a
  exact WilsonPhysicalStationOwnedMixedCourse.original R L fac F J₀ H rows needs (quantity R e n)
    (menu R e room.site room.compact room.clear extra) hg roofs lead bliss below

end YM.Integration.WilsonPhysicalStationMixedWickCollege
end
