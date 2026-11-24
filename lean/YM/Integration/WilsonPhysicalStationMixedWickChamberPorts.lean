import YM.Integration.WilsonPhysicalStationMixedWickCollege
import YM.Integration.WilsonPhysicalStationMixedWickPlacement
import YM.Integration.WilsonPhysicalStationOwnedMixedCourse

/-! A fixed generic lower reference and its actual original thermal election. -/
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickChamberPorts
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
def grade (e h:ℕ):Bool→ℕ | false=>e | true=>h
abbrev port (i:ℕ):Type:=Σp:Bool×Bool,
  (R.family.labels.level (grade (lo i) (hi i) p.2)).Index × Signed × Fin 2
variable (counted:ℕ→ℕ)(more:∀d,Fin (counted d)→Slot R.family)
def quantity (D:ℕ):ℕ:=Fintype.card ((Σi:Fin (D+1),port R lo hi i) ⊕ Fin (counted D))
def contact (i:ℕ)(left right:Bool)(b:(R.family.labels.level (grade (lo i) (hi i) right)).Index)
    (s:Signed)(v:Fin 2):Slot R.family:=
  let room:=chosen R (S:=S) book (lo i) (ax i)
  ⟨grade (lo i) (hi i) left,grade (lo i) (hi i) right,b,s,v,room.site,room.compact,room.clear⟩
def ledger (D:ℕ)(s:Fin (quantity R lo hi counted D)):Slot R.family:=
  Sum.elim (fun u : (Σi:Fin (D+1),port R lo hi i) =>
    contact R (S:=S) book lo hi ax u.1 u.2.1.1 u.2.1.2 u.2.2.1 u.2.2.2.1 u.2.2.2.2)
    (more D) ((Fintype.equivFin _).symm s)
theorem booked (D:ℕ)(i:Fin (D+1))(l r:Bool)
    (b:(R.family.labels.level (grade (lo i) (hi i) r)).Index)(s:Signed)(v:Fin 2):
    ∃j,ledger R (S:=S) book lo hi ax counted more D j=contact R (S:=S) book lo hi ax i l r b s v:=by
  refine ⟨Fintype.equivFin _ (Sum.inl ⟨i,⟨(l,r),b,s,v⟩⟩),?_⟩
  simp [ledger]
theorem added (D:ℕ)(i:Fin (counted D)):
    ∃j,ledger R (S:=S) book lo hi ax counted more D j=more D i:=by
  refine ⟨Fintype.equivFin _ (Sum.inr i),?_⟩
  simp [ledger]
include L fac in
theorem original (hg:G.Simple)(roofs:R2I.RG05Joint.ReporterRoofs.Roofed R.kit)
    (lead:Leading F J₀)(bliss:Bliss F l arch H)(below:(l:Filter _)≤f.fuse):
    Grant R F (l:=l) J₀ H (arch:=arch) rows needs (quantity R lo hi counted) (ledger R (S:=S) book lo hi ax counted more) hg:=
  WilsonPhysicalStationOwnedMixedCourse.original R L fac F J₀ H rows needs
    (quantity R lo hi counted) (ledger R (S:=S) book lo hi ax counted more) hg roofs lead bliss below

end YM.Integration.WilsonPhysicalStationMixedWickChamberPorts
end
