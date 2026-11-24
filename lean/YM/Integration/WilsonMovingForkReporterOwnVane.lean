import YM.Integration.WilsonMovingForkReporterBasisVisits

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterOwnVane
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


abbrev Accepted := {s:Ioc (0:ℝ) radius // 1 ≤ grade (station s)}

theorem original
    (issued:WilsonMovingForkReporterRankSurvey.Books (F:=f) R B O χ H b price c P grade start radius station offset count tests)
    (legal:∀s:Ioc (0:ℝ) radius, offset s∈Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b (grade (station s))))
    (finance:WilsonMovingForkReporterBasisSurvey.Cleared R B O χ b price P grade start count tests):
    ∃Z:∀_s:Accepted grade station,∀k:{k:ℕ // start<k},ℕ→ℕ→TableL R.family (grade k),
      ∀s:Accepted grade station,
        let k:=station s.val
        let pan:=P (grade k) (offset s.val) 0
        let V:=WilsonMovingForkReporterOriginalCouncil.reporters R (grade k) k
          (b (grade k) 0) (c (grade k)) (Z s k) (offset s.val)
        Named (f:=f) R B O χ H price count tests pan V ∧
        ∀h,∀within:h≤grade k,WilsonMovingForkReporterBasisVisits.Seen (f:=f) R B O χ H price count tests pan
          (WilsonMovingForkReporterRestriction.vane within V) := by
  have vendors (s:Accepted grade station) := issued (fun _=>s.val) (fun _=>s.val) (fun _=>s.property)
  choose stock pay named using vendors
  refine ⟨fun s k=>stock s 0 k,?_⟩
  intro s k pan V
  have marked : Named (f:=f) R B O χ H price count tests pan V := (named s 0).1
  refine ⟨marked,?_⟩
  intro h within
  have got:=WilsonMovingForkReporterRankFilament.narrow (f:=f) R B O χ H price count tests pan V within marked
  obtain ⟨checked,ink,_⟩:=got
  obtain ⟨ripe,basis⟩:=finance k k.property
  refine ⟨checked,ink,?_⟩
  intro a deep retained
  exact WilsonMovingForkReporterBasisRows.original R B O χ _ _ _ retained checked ink ripe
    (basis (offset s.val) (legal s.val) 0 a deep)

end YM.Integration.WilsonMovingForkReporterOwnVane
end
