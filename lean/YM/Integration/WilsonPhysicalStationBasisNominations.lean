import YM.Integration.WilsonPhysicalStationBasisJury
/-! All raw columns and reflected detectors of a fixed finite test are nominated on the original pre-cutoff menu. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationBasisNominations
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
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus MergeProof Matric Gram
open PhysicalNext.Repeat.Legato Bandage Campaign
open Next.Foundations OPE Work.G08
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent


open WilsonMovingForkReporterFixedRanks (Axes)
open WilsonMovingForkReporterRankTables (Named)
open WilsonMovingForkReporterPostedRanks (paid)
variable {G:Gauge} (R:Run G) (B:Binding R.family) (O:HaarBudget G) (χ:ChartRatio G)
    {f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
    (H:(Bel R.family.book).Hierarchy) {arch:Arch R.family}
    (price:ℕ→ℝ) (count:ℕ→ℕ) (tests:∀d,Fin (count d)→Axes R.family)
    (F:Final R.family f S) (J₀:ℝ→tower S)
local notation "C"=>R.family


open WilsonPhysicalStationBasisBallot (Seats)
open WilsonPhysicalStationBasisJury (Row Menu bill)
variable {h:ℕ}{D:Type*}[Fintype D](rows:D→Row R.family h)
abbrev Names := (j:D) × Seats R.family h (rows j).q
def size (_:ℕ):ℕ:=Fintype.card (Names R rows)
def exhibit (d:ℕ)(j:Fin (size R rows d)):Axes R.family:=
  let a:Names R rows:=(Fintype.equivFin (Names R rows)).symm j
  bill R rows a.1 a.2
theorem original : Menu R (size R rows) (exhibit R rows) rows:=by
  apply Filter.Eventually.of_forall
  intro d t a
  refine ⟨Fintype.equivFin (Names R rows) ⟨t,a⟩,?_⟩
  exact congrArg (fun k:Names R rows=>bill R rows k.1 k.2) ((Fintype.equivFin (Names R rows)).symm_apply_apply ⟨t,a⟩)
end YM.Integration.WilsonPhysicalStationBasisNominations
end
