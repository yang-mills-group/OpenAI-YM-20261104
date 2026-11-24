import YM.Integration.WilsonPhysicalStationMixedWickActionSchedule
import YM.Integration.WilsonPhysicalStationMixedWickBranch

/-! An original before-regulator calendar pays the signed branch and both trace frames. -/
set_option quotPrecheck false
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
universe u
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickBranchSchedule
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
variable (B:Binding R.family)(O:HaarBudget G)(price:ℕ→ℝ)(b:ℕ→Fin 3→ℝ)(c:ℕ→ℝ)
    (P:∀d,ℝ→Fin 3→Tapes.Panel d)(grade:ℕ→ℕ){start:ℕ}{radius:ℝ}
    (station:Ioc (0:ℝ) radius→{k:ℕ // start < k})(offset:Ioc (0:ℝ) radius→ℝ)

open MS MS.Land MS.Menus MS.Theater XSpace.Structure1 Local.Physical
open WilsonMovingForkReporterMixedBasis (Slot)
open WilsonPhysicalStationMixedWickChamberPorts (quantity ledger)
variable (book:Deck G)(lo hi:ℕ→ℕ)(ax:ℕ→Axis)(counted:ℕ→ℕ)(more:∀d,Fin (counted d)→Slot R.family)
local notation "M₀" => ledger R (S:=S) book lo hi ax counted more

open Spec OPE Climb
variable (almanac:EveryPhase.Almanac F)(reader:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (cohort:Ultrafilter (ℕ×ℕ)→Prop)
open Maxwell.Free
def Account (simple:G.Simple):Prop:=
  ∃(B:Binding R.family),B.prices=R.metals.K ∧ ∃(O:HaarBudget G)(price:ℕ→ℝ)(b:ℕ→Fin 3→ℝ)
     (P:∀d,ℝ→Fin 3→Tapes.Panel d)(c:ℕ→ℝ)(grade:ℕ→ℕ)(start:ℕ)(radius:ℝ),0 < radius ∧
     ∃(station:Ioc (0:ℝ) radius→{k:ℕ // start < k})(offset:Ioc (0:ℝ) radius→ℝ),
      (∀s:Ioc (0:ℝ) radius,offset s∈Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b (grade (station s)))) ∧
      (∀s u:Ioc (0:ℝ) radius,(s:ℝ)≤u→(u:ℝ)≤2*(s:ℝ)→
        (station u).val≤(station s).val ∧ (station s).val≤(station u).val+1) ∧
      (∀D:ℕ,∃ε>(0:ℝ),∀s:Ioc (0:ℝ) radius,(s:ℝ)<ε→D≤grade (station s)) ∧
      (∀k>start,needs (grade k) (P (grade k)) (c (grade k)) ≤ k) ∧
      (∀s:Ioc (0:ℝ) radius,(s:ℝ)=Station.gap R.family.path.levels (b (grade (station s)) 0+offset s) (station s)) ∧
      WilsonMovingForkReporterMixedSurvey.Mixed R B O (Next.Foundations.chart G) b price P grade start (quantity R lo hi counted) M₀ ∧
      WilsonMovingForkReporterBasisSurvey.Cleared R B O (Next.Foundations.chart G) b price P grade start (size R rows) (exhibit R rows) ∧
      WilsonMovingForkReporterRankSurvey.Books (F:=f) R B O (Next.Foundations.chart G) H b price c P grade start
        radius station offset (size R rows) (exhibit R rows) ∧
      (∀i,Menu R (size R rows) (exhibit R rows) (rows i)) ∧
      WilsonPhysicalStationMixedWickBranch.Released.{u} R B O (Next.Foundations.chart G) (l:=l) H (arch:=arch) price (size R rows) (exhibit R rows)
        F J₀ b c P grade station offset book lo hi ax counted more almanac reader cohort simple

theorem purchased (simple:G.Simple)(below:(l:Filter _)≤f.fuse)(store:Store G)
    (grades:∀e:ℕ,∃i,lo i=e ∧ hi i=e+1)
    (stock:WilsonPhysicalStationMixedWickActionSchedule.Issued.{u} R F (l:=l) J₀ H (arch:=arch) rows needs book lo hi ax counted more almanac reader cohort simple):
    Account.{u} R F (l:=l) J₀ H (arch:=arch) rows needs book lo hi ax counted more almanac reader cohort simple:=by
  obtain ⟨B,orig,O,price,b,P,c,grade,start,radius,pos,station,offset,legal,adjacent,late,floors,housed,mixed,cleared,books,menu,field⟩:=stock
  refine ⟨B,orig,O,price,b,P,c,grade,start,radius,pos,station,offset,legal,adjacent,late,floors,housed,mixed,cleared,books,menu,?_⟩
  exact WilsonPhysicalStationMixedWickBranch.original R B O (Next.Foundations.chart G) H price (size R rows) (exhibit R rows)
    F J₀ b c P grade station offset book lo hi ax counted more almanac reader cohort simple store grades below pos
    books housed adjacent late field

include L in
theorem original (simple:G.Simple)(roofs:R2I.RG05Joint.ReporterRoofs.Roofed R.kit)
    (run:WilsonViewerElectedHierarchy.Selected.{u} F almanac reader J₀ H arch l simple cohort)
    (finance:WilsonPhysicalStationMixedWickPose.Finance (Y:=l) (Z:=arch) simple F H)
    (slow:WilsonWindowReportingPace.Slow R.kit)(wide:∀j,1≤(R.family.path.levels.budget j).supportExponent)
    (grades:∀e:ℕ,∃i,lo i=e ∧ hi i=e+1):
    Account.{u} R F (l:=l) J₀ H (arch:=arch) rows needs book lo hi ax counted more almanac reader cohort simple:=by
  obtain ⟨store⟩:=XSpace.Normalize.equipped simple
  apply purchased R F J₀ H rows needs book lo hi ax counted more almanac reader cohort simple run.original store grades
  apply WilsonPhysicalStationMixedWickActionSchedule.original R L F J₀ H rows needs book lo hi ax counted more almanac reader cohort simple run slow wide
  exact WilsonPhysicalStationMixedWickCalibratedSchedule.original R L F J₀ H rows needs book lo hi ax counted more almanac reader cohort simple roofs run finance

end YM.Integration.WilsonPhysicalStationMixedWickBranchSchedule
end
