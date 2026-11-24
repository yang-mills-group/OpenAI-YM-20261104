import YM.Integration.WilsonMeasuredSignedActionOwnedIncome
import YM.Integration.WilsonPhysicalStationOwnedTableSchool
/-! The signed Ward and reflected source receipts for the very programme
selected by the physically owned first-crossing school. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionOwnedSchool
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

def Bought (simple:G.Simple):Prop:=
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
       Issued F (H:=H) (l:=l) (z:=arch) cap V J₀ J

theorem original (simple:G.Simple)(bliss:Bliss F l arch H)
    (located:∀s:Ioc (0:ℝ) radius,(s:ℝ)=Station.gap R.family.path.levels
      (b (grade (station s)) 0+offset s) (station s))
    (large:∀D:ℕ,∃e>(0:ℝ),∀s:Ioc (0:ℝ) radius,(s:ℝ)<e → D≤grade (station s))
    (school:School R B O χ (l:=l) H (arch:=arch) price count tests F J₀ b c P grade station offset simple):
    Bought R B O χ (l:=l) H (arch:=arch) price count tests F J₀ b c P grade station offset simple:=by
  obtain ⟨δ,pos,incl,X,named,J,lead,cost,spin,staff,neighbors⟩:=school
  let cap(s:Ioc (0:ℝ) δ):=grade (station (lift incl s))
  let V:=home R b c grade station offset incl X
  have position(s:Ioc (0:ℝ) δ):(V s).wheel.r=s.val:=(located (lift incl s)).symm
  have calendar(xs:ℕ→Ioc (0:ℝ) δ)(vanish:Tendsto (fun i=>(xs i).val) atTop (𝓝 0)):
      Tendsto (fun i=>cap (xs i)) atTop atTop ∧ Tendsto (fun i=>(V (xs i)).k) atTop atTop:=
    dates grade station (fun i=>lift incl (xs i)) vanish large
  refine ⟨δ,pos,incl,X,named,J,lead,cost,spin,staff,neighbors,?_⟩
  exact WilsonMeasuredSignedActionOwnedIncome.original F simple bliss pos cap V J₀ J position
    (fun s=>(named s).1.choose) calendar staff

end YM.Integration.WilsonMeasuredSignedActionOwnedSchool
end
