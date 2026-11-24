import YM.Integration.WilsonPhysicalStationOwnedTableSchool
import YM.Integration.WilsonMovingForkReporterMixedHouses
import YM.Integration.WilsonMeasuredPublicEntranceNativeSchool
import YM.Integration.WilsonMovingForkReporterOwnVaneWidth
/-! One physical frame and one original table at each radius before choosing either sequence of observations. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationOwnedMixedSchool
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


open PhysicalNext.Repeat Lotus MergeProof PhysicalNext.Repeat.Legato.Bandage Campaign
open Next.Foundations OPE Work.G08
open WilsonMeasuredPublicEntranceNativeSchool (lift home)
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


open WilsonMeasuredPublicEntranceNativeFrame WilsonMeasuredPublicEntranceNativeStaff
open PhysMS.Frame
open private dates from YM.Integration.WilsonMovingForkReporterMeasuredRadii

open WilsonPhysicalStationOwnedTableSchool (Neighbors)
variable (qty:ℕ→ℕ)(menu:∀d,Fin (qty d)→WilsonMovingForkReporterMixedBasis.Slot R.family)

def School (simple:G.Simple):Prop:=
    ∃(δ:ℝ)(_positive:0<δ)(sub:δ≤radius)
      (X:∀s:Ioc (0:ℝ) δ,ℕ→ℕ→TableL R.family (grade (station (lift sub s)))),
      let cap:=fun s=>grade (station (lift sub s))
      let V:=home R b c grade station offset sub X
      (∀s,let pan:=P (cap s) (offset (lift sub s)) 0
          Named (f:=f) R B O χ H price count tests pan (V s) ∧
          ∀h,∀w:h≤cap s,WilsonMovingForkReporterBasisVisits.Seen (f:=f) R B O χ H price count tests pan
            (WilsonMovingForkReporterRestriction.vane w (V s))) ∧
      (∀s,∀h,∀w:h≤cap s,WilsonMovingForkReporterMixedHouses.Held (f:=f) R B O χ H price qty menu
        (P (cap s) (offset (lift sub s)) 0) (WilsonMovingForkReporterRestriction.vane w (V s))) ∧
      ∃J:ℝ→tower S,Leading F J ∧ localCost trail (atRadius l cap V J₀) J ∧
        (∀d,∀ᶠr in trail,obedient F H (J r) d) ∧
        (∀m,∀ᶠr in trail,Receipt (Y:=l) simple F H r (atRadius l cap V J₀ r) (J r) m) ∧ Neighbors R H count tests F (l:=l) (arch:=arch) cap V J

variable {T:Campaign R}(L:Pillars R T)(fac:Facilities R.family f S)
include L fac in
theorem original (lead:Leading F J₀)(simple:G.Simple)(bliss:Bliss F l arch H)(below:(l:Filter _)≤f.fuse)(rp:0<radius)
    (issued:WilsonMovingForkReporterRankSurvey.Books (F:=f) R B O χ H b price c P grade start radius station offset count tests)
    (legal:∀s:Ioc (0:ℝ) radius, offset s∈Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b (grade (station s))))
    (finance:WilsonMovingForkReporterBasisSurvey.Cleared R B O χ b price P grade start count tests)
    (mixed:WilsonMovingForkReporterMixedSurvey.Mixed R B O χ b price P grade start qty menu)
    (located:∀s:Ioc (0:ℝ) radius,(s:ℝ)=Station.gap R.family.path.levels
      (b (grade (station s)) 0+offset s) (station s))
    (adjacent:∀s u:Ioc (0:ℝ) radius,(s:ℝ)≤u→(u:ℝ)≤2*(s:ℝ)→
      (station u).val≤(station s).val ∧ (station s).val≤(station u).val+1)
    (large:∀D:ℕ,∃e>(0:ℝ),∀s:Ioc (0:ℝ) radius,(s:ℝ)<e → D≤grade (station s)):
    School R B O χ (l:=l) H (arch:=arch) price count tests F J₀ b c P grade station offset qty menu simple:=by
  obtain ⟨δ,pos,sub,X,named,J,leading,cost,spins,close,neighbors⟩:=
    WilsonPhysicalStationOwnedTableSchool.original R B O χ H price count tests F J₀ b c P grade station offset
      L fac lead simple bliss below rp issued legal finance located adjacent large
  refine ⟨δ,pos,sub,X,named,?_,J,leading,cost,spins,close,neighbors⟩
  intro s h bound
  exact WilsonMovingForkReporterMixedHouses.at_date R B O χ H price count tests b P grade qty menu
    finance mixed (station (lift sub s)) (offset (lift sub s)) (legal (lift sub s))
    (WilsonMovingForkReporterRestriction.vane bound (home R b c grade station offset sub X s)) rfl ((named s).2 h bound)

end YM.Integration.WilsonPhysicalStationOwnedMixedSchool
end
