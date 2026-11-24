import YM.Integration.WilsonMovingForkReporterBasisSurvey
import YM.Integration.WilsonMovingForkReporterBasisRows
import YM.Integration.WilsonMovingForkReporterMeasuredRadii

/-! All raw input rows at the two actual stations of the selected physical Scribe. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterBasisVisits
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


open WilsonMovingForkReporterFixedRanks (Axes)
open WilsonMovingForkReporterRankTables (Named)
open WilsonMovingForkReporterPostedRanks (paid)
variable {G:Gauge} (R:Run G) (B:Binding R.family) (O:HaarBudget G) (χ:ChartRatio G)
    {f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
    (H:(Bel R.family.book).Hierarchy) {arch:Arch R.family}
    (price:ℕ→ℝ) (count:ℕ→ℕ) (tests:∀d,Fin (count d)→Axes R.family)
    (F:Final R.family f S) (J₀:ℝ→tower S)
local notation "C"=>R.family


open WilsonMovingForkReporterRankFilament (Kept)
variable (b:ℕ→Fin 3→ℝ) (c:ℕ→ℝ) (P:∀d,ℝ→Fin 3→Tapes.Panel d) (grade:ℕ→ℕ)
    {start:ℕ} {radius:ℝ} (station:Ioc (0:ℝ) radius→{k:ℕ // start<k}) (offset:Ioc (0:ℝ) radius→ℝ)

open WilsonMovingForkReporterMeasuredRadii (observed)
variable (Y:∀ (_:ℕ) (k:{k:ℕ // start<k}),ℕ→ℕ→TableL R.family (grade k))
    (outer inner:ℕ→Ioc (0:ℝ) radius)
variable (pick:Pair (fun i=>WilsonMovingForkReporterMeasuredRadii.observed R b c grade station offset Y (outer i) i)
  (fun i=>WilsonMovingForkReporterMeasuredRadii.observed R b c grade station offset Y (inner i) i))

    (legal:∀s:Ioc (0:ℝ) radius, offset s∈Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b (grade (station s))))
    (finance:WilsonMovingForkReporterBasisSurvey.Cleared R B O χ b price P grade start count tests)

def Seen {D h:ℕ} (pan:Tapes.Panel D) (V:Vane R.family h) : Prop :=
  ∃checked:V.checked f H h,
    WilsonMovingForkReporterNamedInk.Filed B R.makes O χ pan V (MergeProof.East.trays D) (price D) ∧
    ∀s:Fin (count D),100*((tests D s).weight+1)≤D → ∀hs:(tests D s).weight≤h,
      WilsonMovingForkReporterBasisRows.Sold R V (tests D s) hs D checked

include finance legal in
theorem take (y:Ioc (0:ℝ) radius) (i:ℕ) {h:ℕ} (small:h≤grade (station y))
    (kept:Kept (f:=f) R B O χ H price count tests (P (grade (station y)) (offset y) 0)
       (WilsonMovingForkReporterRestriction.vane small (observed R b c grade station offset Y y i))) :
    Seen (f:=f) R B O χ H price count tests (P (grade (station y)) (offset y) 0)
       (WilsonMovingForkReporterRestriction.vane small (observed R b c grade station offset Y y i)) := by
  obtain ⟨checked,ink,_⟩:=kept
  obtain ⟨ripe,basis⟩:=finance (station y) (station y).property
  refine ⟨checked,ink,?_⟩
  intro t deep retained
  exact WilsonMovingForkReporterBasisRows.original R B O χ _ _ _ retained checked ink ripe
    (basis (offset y) (legal y) 0 t deep)

include finance legal in
theorem original
    (kept:∀i,Kept (f:=f) R B O χ H price count tests
        (P (grade (station (outer (pick.pick i)))) (offset (outer (pick.pick i))) 0) (pick.report (2*i)) ∧
      Kept (f:=f) R B O χ H price count tests
        (P (grade (station (inner (pick.pick i)))) (offset (inner (pick.pick i))) 0) (pick.report (2*i+1))) (i:ℕ) :
    Seen (f:=f) R B O χ H price count tests
        (P (grade (station (outer (pick.pick i)))) (offset (outer (pick.pick i))) 0) (pick.report (2*i)) ∧
    Seen (f:=f) R B O χ H price count tests
        (P (grade (station (inner (pick.pick i)))) (offset (inner (pick.pick i))) 0) (pick.report (2*i+1)) := by
  have onFile:=kept i
  rw [even,odd] at onFile ⊢
  exact ⟨take R B O χ H price count tests b c P grade station offset Y legal finance
           (outer (pick.pick i)) _ (pick.outer i) onFile.1,
         take R B O χ H price count tests b c P grade station offset Y legal finance
           (inner (pick.pick i)) _ (pick.inner i) onFile.2⟩

end YM.Integration.WilsonMovingForkReporterBasisVisits
end
