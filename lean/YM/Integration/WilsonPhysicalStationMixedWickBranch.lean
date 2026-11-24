import YM.Integration.WilsonPhysicalStationMixedWickAction
import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerCampus

/-! The original signed branch and its posed trace calibration use the same measured fields. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
universe u
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickBranch
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

open Spec OPE Climb
variable (almanac:EveryPhase.Almanac F)(reader:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (cohort:Ultrafilter (ℕ×ℕ)→Prop)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMeasuredSignedActionOwnedIncome (Issued)
open WilsonMeasuredSignedActionReleased (Licensed)
open WilsonMeasuredSignedActionOwnedBook (sub)
open OPE
variable {T₀:Campaign R}(W₀:Campaign.Pillars R T₀)
open Maxwell.Free
def Released (simple:G.Simple):Prop:=
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
        WilsonPhysicalStationMixedWickPaired.Listening R F (l:=l) J H (arch:=arch) B O χ price count tests cap V
          (fun s=>P (cap s) (offset (lift sub s)) 0) book lo hi ax counted more ∧
        ∃Jc:ℝ→tower S,localCost trail J Jc ∧ localCost trail (atRadius l cap V J₀) Jc ∧
          WilsonPhysicalStationMixedWickPose.Receipt (Y:=l) (Z:=arch) simple F H J Jc ∧
          WilsonViewerElectedHierarchy.Selected.{u} F almanac reader Jc H arch l simple cohort ∧
          WilsonPhysicalStationMixedEnrolledStream.Listening R F (ℓ:=l) (H:=H) (arch:=arch) J B O χ price count tests cap V
            (fun s=>P (cap s) (offset (lift sub s)) 0) book lo hi ax counted more ∧
          (∀d:ℕ,∀a:ℝ,0<a→WilsonPhysicalPositionHalfRange.uniform J d a) ∧
          Issued F (H:=H) (l:=l) (z:=arch) cap V J₀ J ∧
          Issued F (H:=H) (l:=l) (z:=arch) cap V J₀ Jc ∧
          ∀(I:Type)[Fintype I][DecidableEq I][Nonempty I](base:ℕ)
            (Γ:WilsonViewerReportingGrid.Grid (ℓ:=l) F base (wilson arch))(D:ℕ),
            ∃t:ℕ,∃ε:ℝ,0<ε ∧ ∃incl:ε≤δ,∃books:(s:{s:ℝ // 0<s ∧ s<ε})→Book F (l:=l) H arch D t s.val,
              (∀s,(books s).k=cap (WilsonMeasuredSignedActionOwnedBook.sub incl s) ∧ (books s).W.k=(V (WilsonMeasuredSignedActionOwnedBook.sub incl s)).k ∧
                HEq (books s).W (V (WilsonMeasuredSignedActionOwnedBook.sub incl s)) ∧ ∀i:Fin (D+1),(books s).V i=atRadius l cap V J₀ s.val i) ∧
              Licensed F (I:=I) Γ D t books J ∧ Licensed F (I:=I) Γ D t books Jc

theorem original (simple:G.Simple)(store:Store G)(grades:∀e:ℕ,∃i,lo i=e ∧ hi i=e+1)
    (below:(l:Filter _)≤f.fuse)(rp:0<radius)
    (issued:WilsonMovingForkReporterRankSurvey.Books (F:=f) R B O χ H b price c P grade start radius station offset count tests)
    (located:∀s:Ioc (0:ℝ) radius,(s:ℝ)=Station.gap R.family.path.levels (b (grade (station s)) 0+offset s) (station s))
    (adjacent:∀s u:Ioc (0:ℝ) radius,(s:ℝ)≤u→(u:ℝ)≤2*(s:ℝ)→(station u).val≤(station s).val ∧ (station s).val≤(station u).val+1)
    (large:∀D:ℕ,∃ε>(0:ℝ),∀s:Ioc (0:ℝ) radius,(s:ℝ)<ε→D≤grade (station s))
    (awarded:WilsonPhysicalStationMixedWickAction.Served.{u} R B O χ (l:=l) H (arch:=arch) price count tests F J₀ b c P grade station offset book lo hi ax counted more almanac reader cohort simple):
    Released.{u} R B O χ (l:=l) H (arch:=arch) price count tests F J₀ b c P grade station offset book lo hi ax counted more almanac reader cohort simple:=by
  obtain ⟨η,youngAge,onset⟩:=large 1
  let s:Ioc (0:ℝ) radius:=⟨min radius (η/2),lt_min rp (half_pos youngAge),min_le_left ..⟩
  have young:1≤grade (station s):=onset s ((min_le_right radius (η/2)).trans_lt (half_lt_self youngAge))
  have paid:=WilsonMovingForkReporterOwnVaneWidth.original R B O χ H price count tests b c P grade station offset issued ⟨s,young⟩
  have width:∀ᶠj:ℕ in atTop,topL R.family.path.levels j≤R.family.path.levels.clock.monitor j:=
    (eventually_gt_atTop start).mono fun _ j=>paid _ j
  obtain ⟨δ,pos,incl,X,named,held,J,leading,near,duty,staff,neighbors,listening,Jc,change,joint,receipt,selected,unposed,posed,books⟩:=awarded
  let cap(u:Ioc (0:ℝ) δ):=grade (station (lift incl u))
  let V:=home R b c grade station offset incl X
  have stream:=WilsonPhysicalStationMixedEnrolledStream.original R F (ℓ:=l) (H:=H) (arch:=arch) J B O χ price count tests cap V
    (fun u=>P (cap u) (offset (lift incl u)) 0) book lo hi ax counted more simple below width
    (fun u=>(located (lift incl u)).symm) (fun u v tie gap=>adjacent (lift incl u) (lift incl v) tie gap) listening
  refine ⟨δ,pos,incl,X,named,held,J,leading,near,duty,staff,neighbors,listening,Jc,change,joint,receipt,selected,stream,?_,unposed,posed,books⟩
  intro d
  apply WilsonMeasuredPublicEntranceNativeLowerUniform.original R F leading near store
  exact WilsonMeasuredPublicEntranceNativeLowerBooked.original R F J H B O χ price count tests cap V
    (fun s=>P (cap s) (offset (lift incl s)) 0) book lo hi ax counted more
    J₀ pos (fun s=>(located (lift incl s)).symm) grades stream d

end YM.Integration.WilsonPhysicalStationMixedWickBranch
end
