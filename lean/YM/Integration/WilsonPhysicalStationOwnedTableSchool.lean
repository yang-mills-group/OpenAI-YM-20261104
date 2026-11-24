import YM.Integration.WilsonPhysicalStationOwnedTablePair
import YM.Integration.WilsonMeasuredPublicEntranceNativeSchool
import YM.Integration.WilsonMovingForkReporterOwnVaneWidth
/-! One physical frame and one original table at each radius before choosing either sequence of observations. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationOwnedTableSchool
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

def Neighbors {δ:ℝ}(cap:Ioc (0:ℝ) δ→ℕ)(V:∀s,Vane R.family (cap s))(J₁:ℝ→tower S):Prop:=
  ∀outer inner:ℕ→Ioc (0:ℝ) δ,Tendsto (fun i=>(outer i:ℝ)) atTop (𝓝 0)→
    Tendsto (fun i=>(inner i:ℝ)) atTop (𝓝 0)→(∀ᶠi:ℕ in atTop,(inner i:ℝ)<(outer i:ℝ))→
    (∀i,(outer i:ℝ)≤2*(inner i:ℝ))→∃c:Pair (fun i=>V (outer i)) (fun i=>V (inner i)),∃J:Scaling S,
      WilsonPhysicalStationOwnedTablePair.Held R F (l:=l) J₁ H (arch:=arch) count tests cap V outer inner c J

def School (simple:G.Simple):Prop:=
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
        (∀m,∀ᶠr in trail,Receipt (Y:=l) simple F H r (atRadius l cap V J₀ r) (J r) m) ∧ Neighbors R H count tests F (l:=l) (arch:=arch) cap V J

variable {T:Campaign R}(L:Pillars R T)(fac:Facilities R.family f S)
include L fac in
theorem original (lead:Leading F J₀)(simple:G.Simple)(bliss:Bliss F l arch H)(below:(l:Filter _)≤f.fuse)(rp:0<radius)
    (issued:WilsonMovingForkReporterRankSurvey.Books (F:=f) R B O χ H b price c P grade start radius station offset count tests)
    (legal:∀s:Ioc (0:ℝ) radius, offset s∈Icc 0 (WilsonPhysicalPositionWeakRoofSchedule.width b (grade (station s))))
    (finance:WilsonMovingForkReporterBasisSurvey.Cleared R B O χ b price P grade start count tests)
    (located:∀s:Ioc (0:ℝ) radius,(s:ℝ)=Station.gap R.family.path.levels
      (b (grade (station s)) 0+offset s) (station s))
    (adjacent:∀s u:Ioc (0:ℝ) radius,(s:ℝ)≤u→(u:ℝ)≤2*(s:ℝ)→
      (station u).val≤(station s).val ∧ (station s).val≤(station u).val+1)
    (large:∀D:ℕ,∃e>(0:ℝ),∀s:Ioc (0:ℝ) radius,(s:ℝ)<e → D≤grade (station s)):
    School R B O χ (l:=l) H (arch:=arch) price count tests F J₀ b c P grade station offset simple:=by
  obtain ⟨δ,pos,sub,X,named,J₁,lead₁,cost,spins,close⟩:=WilsonMeasuredPublicEntranceNativeSchool.original
    R B O χ H price count tests F J₀ b c P grade station offset lead simple bliss rp issued legal finance located large
  let cap(s:Ioc (0:ℝ) δ):=grade (station (lift sub s))
  let V:=home R b c grade station offset sub X
  refine ⟨δ,pos,sub,X,named,J₁,lead₁,cost,spins,close,?_⟩
  have place(s:Ioc (0:ℝ) δ):(V s).wheel.r=(s:ℝ):=(located (lift sub s)).symm
  have calendar(xs:ℕ→Ioc (0:ℝ) δ)(falls:Tendsto (fun i=>(xs i:ℝ)) atTop (𝓝 0)):
      Tendsto (fun i=>cap (xs i)) atTop atTop ∧ Tendsto (fun i=>(V (xs i)).k) atTop atTop:=
    dates grade station (fun i=>lift sub (xs i)) falls large
  obtain ⟨u,up,late⟩:=large 1
  let witness:Ioc (0:ℝ) radius:=⟨min radius (u/2),lt_min rp (half_pos up),min_le_left ..⟩
  have active:WilsonMovingForkReporterOwnVane.Accepted grade station:=
    ⟨witness,late witness ((min_le_right radius (u/2)).trans_lt (half_lt_self up))⟩
  have roof:=WilsonMovingForkReporterOwnVaneWidth.original R B O χ H price count tests b c P grade station offset issued active
  have house:∀ᶠk:ℕ in atTop,topL R.family.path.levels k≤R.family.path.levels.clock.monitor k:=
    (eventually_gt_atTop start).mono fun k hk=>roof k hk
  intro outer inner fall₀ fall₁ apart comparable
  exact WilsonPhysicalStationOwnedTablePair.original R L fac F J₁ H B O χ price count tests cap V
    (fun s=>P (cap s) (offset (lift sub s)) 0) outer inner lead₁ simple bliss below house place calendar
    (fun s t=>adjacent (lift sub s) (lift sub t)) named fall₀ fall₁ apart comparable

end YM.Integration.WilsonPhysicalStationOwnedTableSchool
end
