import YM.Integration.WilsonMeasuredSignedActionReleased
/-! The retained original staff and its signed action on the same named table. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionCourt
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


open WilsonPhysicalStationOwnedTableSchool (School Neighbors)
open WilsonMeasuredSignedActionOwnedIncome (Issued)
open private dates from YM.Integration.WilsonMovingForkReporterMeasuredRadii


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMeasuredSignedActionOwnedBook (sub)
open WilsonMeasuredSignedActionReleased (Licensed)
open WilsonOriginalMicroscopicGuardedReporters PhysicalNext.Repeat.Legato MergeProof Campaign

def Certified {δ:ℝ}(cap:Ioc (0:ℝ) δ→ℕ)(V:∀s,Vane C (cap s))(J:ℝ→tower S):Prop:=
  ∀(I:Type)[Fintype I][DecidableEq I][Nonempty I]{base:ℕ}
    (Γ:WilsonViewerReportingGrid.Grid (ℓ:=l) F base (wilson arch))(D:ℕ),
    ∃T:ℕ,∃e:ℝ,0<e ∧ ∃incl:e≤δ,∃B:(s:{s:ℝ // 0<s ∧ s<e})→Book F (l:=l) H arch D T s.val,
      (∀s,(B s).k=cap (sub incl s) ∧ (B s).W.k=(V (sub incl s)).k ∧ HEq (B s).W (V (sub incl s)) ∧
        ∀i:Fin (D+1),(B s).V i=atRadius l cap V J₀ s.val i) ∧ Licensed F (I:=I) Γ D T B J

def Earned (simple:G.Simple):Prop:=
    ∃(δ:ℝ)(_positive:0<δ)(sub:δ≤radius)
      (X:∀s:Ioc (0:ℝ) δ,ℕ→ℕ→TableL R.family (grade (station (lift sub s)))),
      let cap:=fun s=>grade (station (lift sub s))
      let V:=home R b c grade station offset sub X
      (∀s,let pan:=P (cap s) (offset (lift sub s)) 0
          Named (f:=f) R B O χ H price count tests pan (V s) ∧
          ∀h,∀w:h≤cap s,WilsonMovingForkReporterBasisVisits.Seen (f:=f) R B O χ H price count tests pan
            (WilsonMovingForkReporterRestriction.vane w (V s))) ∧
      ∃J:ℝ→tower S,Leading F J ∧ localCost trail (atRadius l cap V J₀) J ∧
        (∀d,∀ᶠr in trail,obedient F H (J r) d) ∧
        (∀m,∀ᶠr in trail,Receipt (Y:=l) simple F H r (atRadius l cap V J₀ r) (J r) m) ∧ Neighbors R H count tests F (l:=l) (arch:=arch) cap V J ∧
       Issued F (H:=H) (l:=l) (z:=arch) cap V J₀ J ∧ Certified R H F J₀ (l:=l) (arch:=arch) cap V J


theorem original {programme:Campaign R}(L:Pillars R programme)(simple:G.Simple)(bliss:Bliss F l arch H)
    (slow:WilsonWindowReportingPace.Slow R.kit)(wide:∀j,1≤((C).path.levels.budget j).supportExponent)
    (stock:WilsonMeasuredSignedActionOwnedSchool.Bought R B O χ (l:=l) H (arch:=arch) price count tests
      F J₀ b c P grade station offset simple):
    Earned R B O χ (l:=l) H (arch:=arch) price count tests F J₀ b c P grade station offset simple:=by
  obtain ⟨δ,positive,sub,X,seen,J,lead,salary,fitted,staff,adjacent,pay⟩:=stock
  refine ⟨δ,positive,sub,X,seen,J,lead,salary,fitted,staff,adjacent,pay,?_⟩
  intro I finite dec populated base Γ D
  exact WilsonMeasuredSignedActionReleased.original F L simple bliss slow Γ wide _ _ _ J pay D

end YM.Integration.WilsonMeasuredSignedActionCourt
end
