import YM.Integration.WilsonMovingForkReporterOwnVane
import YM.Integration.WilsonMovingForkReporterMixedSurvey

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterMixedHouses
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



open WilsonMovingForkReporterMixedBasis (Slot Posted)
open WilsonMovingForkReporterOwnVane (Accepted)
variable (qty:ℕ→ℕ)(menu:∀d,Fin (qty d)→Slot R.family)

def Held {D h:ℕ}(P:Tapes.Panel D)(V:Vane R.family h) : Prop :=
  ∃ _:V.checked f H h, WilsonMovingForkReporterNamedInk.Filed B R.makes O χ P V (MergeProof.East.trays D) (price D) ∧
    (D:ℝ)+1≤R.family.path.levels.clock.monitor V.k^(WilsonMovingForkReporterRankCourse.surplus D) ∧
    ∀s:Fin (qty D),100*(max (menu D s).left (menu D s).right+1)≤D→
      Posted B R.makes O χ (menu D s) P V.k (price D)

theorem at_date
    (finance:WilsonMovingForkReporterBasisSurvey.Cleared R B O χ b price P grade start count tests)
    (mixed:WilsonMovingForkReporterMixedSurvey.Mixed R B O χ b price P grade start qty menu)
    (k:{k:ℕ // start<k})(x:ℝ)(legal:x∈Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b (grade k)))
    {h:ℕ}(V:Vane R.family h)(date:V.k=k)
    (studied:WilsonMovingForkReporterBasisVisits.Seen (f:=f) R B O χ H price count tests (P (grade k) x 0) V) :
    Held (f:=f) R B O χ H price qty menu (P (grade k) x 0) V := by
  obtain ⟨check,ink,_⟩:=studied
  refine ⟨check,ink,?_,?_⟩
  · rw [date]; exact (finance k k.2).1
  · intro s active
    rw [date]
    exact mixed k k.2 x legal 0 s active

theorem original
    (issued:WilsonMovingForkReporterRankSurvey.Books (F:=f) R B O χ H b price c P grade start radius station offset count tests)
    (legal:∀s:Ioc (0:ℝ) radius, offset s∈Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b (grade (station s))))
    (finance:WilsonMovingForkReporterBasisSurvey.Cleared R B O χ b price P grade start count tests)
    (mixed:WilsonMovingForkReporterMixedSurvey.Mixed R B O χ b price P grade start qty menu):
    ∃Z:∀_s:Accepted grade station,∀k:{k:ℕ // start<k},ℕ→ℕ→TableL R.family (grade k),
      ∀s:Accepted grade station,
        let k:=station s.val
        let pan:=P (grade k) (offset s.val) 0
        let V:=WilsonMovingForkReporterOriginalCouncil.reporters R (grade k) k
          (b (grade k) 0) (c (grade k)) (Z s k) (offset s.val)
        Named (f:=f) R B O χ H price count tests pan V ∧
        ∀h,∀within:h≤grade k, let W:=WilsonMovingForkReporterRestriction.vane within V
          WilsonMovingForkReporterBasisVisits.Seen (f:=f) R B O χ H price count tests pan W ∧
          Held (f:=f) R B O χ H price qty menu pan W := by
  obtain ⟨Z,shared⟩:=WilsonMovingForkReporterOwnVane.original (f:=f) R B O χ H price count tests b c P grade station offset issued legal finance
  refine ⟨Z,?_⟩
  intro s k pan V
  refine ⟨(shared s).1,?_⟩
  intro h within W
  have seen:=(shared s).2 h within
  exact ⟨seen,at_date R B O χ H price count tests b P grade qty menu finance mixed k (offset s.val) (legal s.val) W rfl seen⟩

end YM.Integration.WilsonMovingForkReporterMixedHouses
end
