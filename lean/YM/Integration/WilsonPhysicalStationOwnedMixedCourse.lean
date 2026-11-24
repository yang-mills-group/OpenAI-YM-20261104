import YM.Integration.WilsonPhysicalStationOwnedMixedSchool
import YM.Integration.WilsonMovingForkReporterMixedSurvey
import YM.Integration.WilsonPhysicalStationOwnedTableNominations
import YM.Integration.WilsonMovingForkReporterBasisOnRun
/-! Original bought weak station at every radius and one common position frame, before neighboring measurements. -/
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationOwnedMixedCourse
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

variable (qty:ℕ→ℕ)(menu:∀d,Fin (qty d)→WilsonMovingForkReporterMixedBasis.Slot R.family)

def Grant (simple:G.Simple):Prop:=
  ∃(B:Binding R.family),B.prices=R.metals.K ∧ ∃(O:HaarBudget G)(price:ℕ→ℝ)(b:ℕ→Fin 3→ℝ)
     (P:∀d,ℝ→Fin 3→Tapes.Panel d)(c:ℕ→ℝ)(grade:ℕ→ℕ)(start:ℕ)(radius:ℝ),0 < radius ∧
     ∃(station:Ioc (0:ℝ) radius→{k:ℕ // start < k})(offset:Ioc (0:ℝ) radius→ℝ),
      (∀k>start,needs (grade k) (P (grade k)) (c (grade k)) ≤ k) ∧
      (∀s:Ioc (0:ℝ) radius,(s:ℝ)=Station.gap R.family.path.levels (b (grade (station s)) 0+offset s) (station s)) ∧
      (∀i,Menu R (size R rows) (exhibit R rows) (rows i)) ∧
      School R B O (Next.Foundations.chart G) (l:=l) H (arch:=arch) price (size R rows) (exhibit R rows)
        F J₀ b c P grade station offset qty menu simple

include L fac in
theorem original (hg:G.Simple)(roofs:R2I.RG05Joint.ReporterRoofs.Roofed R.kit)
    (lead:Leading F J₀)(bliss:Bliss F l arch H)(below:(l:Filter _) ≤ f.fuse):
    Grant R F (l:=l) J₀ H (arch:=arch) rows needs qty menu hg:=by
  obtain ⟨O,price,b,income,grow,large,room⟩:=roofs
  have old:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  obtain ⟨_,_,_,scrim,_,B,_,originalB,_⟩:=old.reception
  have parade:=Next.Rank.East.enclosing R.stories old.freight R.makes
  obtain ⟨P,c,grade,start,radius,pos,station,offset,read,adjacent,late,floors,mixed,finance,issued⟩:=
    WilsonMovingForkReporterMixedSurvey.original R B O (Next.Foundations.chart G) F H hg scrim b price grow large
      (room R.family rfl B originalB R.makes parade) (fun d i hi=>income i d hi) parade
      (size R rows) (exhibit R rows) qty menu needs
  refine ⟨B,originalB,O,price,b,P,c,grade,start,radius,pos,station,offset,floors,fun s=>(read s).2,?_⟩
  refine ⟨WilsonPhysicalStationOwnedTableNominations.original R rows,?_⟩
  exact WilsonPhysicalStationOwnedMixedSchool.original R B O (Next.Foundations.chart G) H price
    (size R rows) (exhibit R rows) F J₀ b c P grade station offset qty menu L fac lead hg bliss below pos
    issued (fun s=>(read s).1) finance mixed (fun s=>(read s).2) adjacent late

end YM.Integration.WilsonPhysicalStationOwnedMixedCourse
end
