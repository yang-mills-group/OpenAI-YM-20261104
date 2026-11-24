import YM.Integration.WilsonPhysicalStationMixedEnrolledStream
import YM.Integration.WilsonMovingForkReporterOwnVaneWidth
import YM.Integration.WilsonPhysicalStationMixedWickCampus
import YM.Integration.WilsonPhysicalStationOwnedMixedSchool
/-! One physical frame and one original table at each radius before choosing either sequence of observations. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedEnrolledCampus
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
open MS MS.Land MS.Menus MS.Theater XSpace.Structure1 Local.Physical
open WilsonMovingForkReporterMixedBasis (Slot)
open WilsonPhysicalStationMixedWickChamberPorts (quantity ledger)
variable (book:Deck G)(lo hi:ℕ→ℕ)(ax:ℕ→Axis)(counted:ℕ→ℕ)(more:∀d,Fin (counted d)→Slot R.family)
local notation "M₀" => ledger R (S:=S) book lo hi ax counted more

def Attained (simple:G.Simple):Prop:=
    ∃(δ:ℝ)(_positive:0<δ)(sub:δ≤radius)
      (X:∀s:Ioc (0:ℝ) δ,ℕ→ℕ→TableL R.family (grade (station (lift sub s)))),
      let cap:=fun s=>grade (station (lift sub s))
      let V:=home R b c grade station offset sub X
      (∀s,let pan:=P (cap s) (offset (lift sub s)) 0
          Named (f:=f) R B O χ H price count tests pan (V s) ∧
          ∀h,∀w:h≤cap s,WilsonMovingForkReporterBasisVisits.Seen (f:=f) R B O χ H price count tests pan
            (WilsonMovingForkReporterRestriction.vane w (V s))) ∧
      (∀s,∀h,∀w:h≤cap s,WilsonMovingForkReporterMixedHouses.Held (f:=f) R B O χ H price (quantity R lo hi counted) M₀
        (P (cap s) (offset (lift sub s)) 0) (WilsonMovingForkReporterRestriction.vane w (V s))) ∧
      ∃J:ℝ→tower S,Leading F J ∧ localCost trail (atRadius l cap V J₀) J ∧
        (∀d,∀ᶠr in trail,obedient F H (J r) d) ∧
        (∀m,∀ᶠr in trail,Receipt (Y:=l) simple F H r (atRadius l cap V J₀ r) (J r) m) ∧ Neighbors R H count tests F (l:=l) (arch:=arch) cap V J ∧
        WilsonPhysicalStationMixedEnrolledStream.Listening R F (ℓ:=l) (H:=H) (arch:=arch) J B O χ price count tests cap V
          (fun s=>P (cap s) (offset (lift sub s)) 0) book lo hi ax counted more


theorem supplied (simple:G.Simple)(below:(l:Filter _)≤f.fuse)(rp:0<radius)
    (issued:WilsonMovingForkReporterRankSurvey.Books (F:=f) R B O χ H b price c P grade start radius station offset count tests)
    (located:∀s:Ioc (0:ℝ) radius,(s:ℝ)=Station.gap R.family.path.levels (b (grade (station s)) 0+offset s) (station s))
    (adjacent:∀s u:Ioc (0:ℝ) radius,(s:ℝ)≤u→(u:ℝ)≤2*(s:ℝ)→
      (station u).val≤(station s).val ∧ (station s).val≤(station u).val+1)
    (large:∀D:ℕ,∃η>(0:ℝ),∀s:Ioc (0:ℝ) radius,(s:ℝ)<η→D≤grade (station s))
    (campus:WilsonPhysicalStationMixedWickCampus.Attained R B O χ (l:=l) H (arch:=arch) price count tests F J₀ b c P grade station offset book lo hi ax counted more simple):
    Attained R B O χ (l:=l) H (arch:=arch) price count tests F J₀ b c P grade station offset book lo hi ax counted more simple:=by
  obtain ⟨η,positive,onset⟩:=large 1
  let s:Ioc (0:ℝ) radius:=⟨min radius (η/2),lt_min rp (half_pos positive),min_le_left ..⟩
  have young:1≤grade (station s):=onset s ((min_le_right radius (η/2)).trans_lt (half_lt_self positive))
  have paid:=WilsonMovingForkReporterOwnVaneWidth.original R B O χ H price count tests b c P grade station offset issued ⟨s,young⟩
  have width:∀ᶠj:ℕ in atTop,topL R.family.path.levels j≤R.family.path.levels.clock.monitor j:=
    (eventually_gt_atTop start).mono fun _ j=>paid _ j
  obtain ⟨δ,pos,sub,X,named,mixed,J,leading,localCash,spins,close,neighbors,listening⟩:=campus
  let cap(u:Ioc (0:ℝ) δ):=grade (station (lift sub u))
  let V:=home R b c grade station offset sub X
  refine ⟨δ,pos,sub,X,named,mixed,J,leading,localCash,spins,close,neighbors,?_⟩
  exact WilsonPhysicalStationMixedEnrolledStream.original R F (ℓ:=l) (H:=H) (arch:=arch) J B O χ price count tests cap V
    (fun u=>P (cap u) (offset (lift sub u)) 0) book lo hi ax counted more simple below width
    (fun u=>(located (lift sub u)).symm) (fun u v tie gap=>adjacent (lift sub u) (lift sub v) tie gap) listening
end YM.Integration.WilsonPhysicalStationMixedEnrolledCampus
end
