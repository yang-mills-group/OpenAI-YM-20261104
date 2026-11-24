import YM.Integration.WilsonPhysicalStationMixedWickBranchSchedule
import YM.Integration.WilsonPhysicalStationMixedWickFinance
import YM.Integration.WilsonPhysicalStationMixedWickGrades
import YM.Integration.WilsonPhysicalStationMixedEnrolledRun
import YM.Integration.WilsonPhysicalWeakPaidElection

/-! Select the genuine Wilson run before every public roster and before the posed trace target. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonPhysicalStationMixedWickOriginalRun
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
open Spec OPE
variable (almanac:EveryPhase.Almanac F)(reader:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (cohort:Ultrafilter (ℕ×ℕ)→Prop)
def Appointed (simple:G.Simple):Prop:=
  ∀{height:ℕ}{slots:Fin height→ℕ}(rows:(i:Fin height)→Fin (slots i)→WilsonPhysicalStationBasisJury.Row R.family (i.val+1))
    (needs:∀d:ℕ,(ℝ→Fin 3→Tapes.Panel d)→ℝ→ℕ)
    (book:Deck G)(lo hi:ℕ→ℕ)(ax:ℕ→Axis)(counted:ℕ→ℕ)(more:∀d,Fin (counted d)→Slot R.family),
    (∀e:ℕ,∃i,lo i=e ∧ hi i=e+1)→WilsonPhysicalStationMixedWickBranchSchedule.Account.{u} R F (l:=l) J₀ H (arch:=arch) rows needs book lo hi ax counted more almanac reader cohort simple

include L in
theorem onFrame (simple:G.Simple)(roofs:R2I.RG05Joint.ReporterRoofs.Roofed R.kit)
    (run:WilsonViewerElectedHierarchy.Selected.{u} F almanac reader J₀ H arch l simple cohort)
    (finance:WilsonPhysicalStationMixedWickPose.Finance (Y:=l) (Z:=arch) simple F H)
    (slow:WilsonWindowReportingPace.Slow R.kit)(wide:∀j,1≤(R.family.path.levels.budget j).supportExponent):
    Appointed.{u} R F (l:=l) J₀ H (arch:=arch) almanac reader cohort simple:=by
  intro height slots rows needs book lo hi ax cnt more grades
  exact WilsonPhysicalStationMixedWickBranchSchedule.original R L F J₀ H rows needs book lo hi ax cnt more
    almanac reader cohort simple roofs run finance slow wide grades

theorem all_grades (simple:G.Simple)(stock:Appointed.{u} R F (l:=l) J₀ H (arch:=arch) almanac reader cohort simple):
    WilsonPhysicalStationMixedWickBranchSchedule.Account.{u} R F (l:=l) J₀ H (arch:=arch) rows needs book
      WilsonPhysicalStationMixedWickGrades.lower WilsonPhysicalStationMixedWickGrades.upper WilsonPhysicalStationMixedWickGrades.axis
      counted more almanac reader cohort simple:=by
  apply stock
  intro e
  refine ⟨WilsonPhysicalStationMixedWickGrades.entry e (e+1) 0,?_,?_⟩
  · simp only [WilsonPhysicalStationMixedWickGrades.lower,WilsonPhysicalStationMixedWickGrades.booked]
  · simp only [WilsonPhysicalStationMixedWickGrades.upper,WilsonPhysicalStationMixedWickGrades.booked]

end YM.Integration.WilsonPhysicalStationMixedWickOriginalRun
namespace YM.Integration.WilsonOriginalGeneralRosterOriginalCourse

open Climb Lattice Filter Function Set Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction GapsContact.Seams GapsContact.Ascent
open RG RG.Supply MS MS.Land FVA2 FVA2.Register
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonReflectedMixedMasterSchool (field)
open WilsonOriginalGeneralRosterUnion (Row)
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open XSpace
open WilsonOriginalOpticalSchedule (prepared)
open scoped Classical Topology
variable {G:Gauge}

theorem calibrated_ports (axis:Axis)(simple:G.Simple){ε:ℝ}(positive:0<ε)(σ:WilsonOriginalAllOrderCourse.Schedule G):
    ∃(R:Run G)(T:Campaign R)(W:Campaign.Pillars R T),
    RestoredBooking WilsonIndependentRestoredPublicRates.tolerance R.b ∧ WilsonMovingForkReporterBasisOnRun.Banks R ∧ ∃p:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε (prepared σ) R T W,
    ∃lamp:WilsonReportLampForecast.Ready R.family.path.levels,∃paths:FundedOriginalVacuumPaths.prices R.kit,
    Lower p paths lamp ∧
    ∀(cohort:Ultrafilter (ℕ×ℕ)→Prop),(∀(v:Extraction.Order)(l:Ultrafilter (ℕ×ℕ)),(l:Filter (ℕ×ℕ))≤v.fuse→cohort l)→
      ∀v:Extraction.Order,∃(w:Extraction.Order)(S:Table R.family.book)(F:Final R.family (v.refine w) S)
      (L:EveryPhase.Almanac F)(Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(H:(Bel R.family.book).Hierarchy),
      ∃z:Trace.Terrace.Arch R.family,∃l:Ultrafilter (ℕ×ℕ),∃J:ℝ→PhysMS.tower S,
      ∃chosen:WilsonViewerElectedHierarchy.Selected.{u} F L Q J H z l simple cohort,
        Household p chosen.bliss chosen.leading chosen.obeys chosen.original lamp ∧
        Nonempty (WilsonPhysicalAllGradeWeakElection.Assignment F J H l simple) ∧
        WilsonPhysicalStationMixedWickPose.Finance (Y:=l) (Z:=z) simple F H ∧
        (∀Jc:ℝ→PhysMS.tower S,∀posed:WilsonViewerElectedHierarchy.Selected.{u} F L Q Jc H z l simple cohort,
          Household p posed.bliss posed.leading posed.obeys posed.original lamp) ∧
        WilsonPhysicalStationMixedWickOriginalRun.Appointed.{u} R F (l:=l) J H (arch:=z) L Q cohort simple:=by
  obtain ⟨R,T,W,⟨roofs,restored⟩,p,bank,lamp,paths⟩:=WilsonOriginalPhysicalFirstEntryOwnerFinance.roofed.{u}
    WilsonIndependentRestoredPublicRates.tolerance WilsonIndependentRestoredPublicRates.positive axis simple positive (prepared σ)
  refine ⟨R,T,W,restored,WilsonMovingForkReporterBasisOnRun.original R simple roofs,p,lamp,paths,?_,?_⟩
  · intro I B U _ _ _ D term h d M E main pair precision outside w wanted
    exact WilsonOriginalGeneralRosterLowerInvoice.original (U:=U) p paths lamp term h d M E main pair precision outside w wanted
  intro cohort eligible v
  obtain ⟨fund,slow,_⟩:=WilsonPhysicalCommonElection.finances p
  let lender:=OPE.Stroke.PoleC (OPE.Stroke.Earτ axis simple)
  have lanes:=WilsonMatrixTicketFuelPrice.lanes R lender.price lender.charge p.nested.1
  obtain ⟨w,S,F,L,Q,J,H,z,l,chosen,assignment,finance⟩:=
    WilsonPhysicalStationMixedWickFinance.original R simple cohort W fund lanes eligible v
  have homes (Jc:ℝ→PhysMS.tower S)(posed:WilsonViewerElectedHierarchy.Selected.{u} F L Q Jc H z l simple cohort):
      Household p posed.bliss posed.leading posed.obeys posed.original lamp:=by
    have physical:=WilsonOriginalGeneralRosterHomePhysical.onFrame p bank lamp F Jc posed.bliss posed.leading posed.obeys posed.facilities
    exact onFrame p posed.bliss posed.leading posed.obeys posed.original lamp
      (WilsonOriginalGeneralRosterHomeRegistered.onFrame p posed.bliss posed.leading posed.obeys posed.original physical)
  refine ⟨w,S,F,L,Q,H,z,l,J,chosen,homes J chosen,assignment,finance,homes,?_⟩
  exact WilsonPhysicalStationMixedWickOriginalRun.onFrame R W F J H L Q cohort simple roofs chosen finance slow
    (fun j=>by rw [p.support j]; norm_num)

end YM.Integration.WilsonOriginalGeneralRosterOriginalCourse
end
