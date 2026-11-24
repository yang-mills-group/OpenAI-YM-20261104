import YM.Integration.WilsonPhysicalStationMixedWickCalibrated
import YM.Integration.WilsonMeasuredSignedActionPosedSchool

/-! One public field book, measured before and after the original trace calibration. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
universe u
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickAction
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
def Served (simple:G.Simple):Prop:=
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
          Issued F (H:=H) (l:=l) (z:=arch) cap V J₀ J ∧
          Issued F (H:=H) (l:=l) (z:=arch) cap V J₀ Jc ∧
          ∀(I:Type)[Fintype I][DecidableEq I][Nonempty I](base:ℕ)
            (Γ:WilsonViewerReportingGrid.Grid (ℓ:=l) F base (wilson arch))(D:ℕ),
            ∃t:ℕ,∃ε:ℝ,0<ε ∧ ∃incl:ε≤δ,∃books:(s:{s:ℝ // 0<s ∧ s<ε})→Book F (l:=l) H arch D t s.val,
              (∀s,(books s).k=cap (WilsonMeasuredSignedActionOwnedBook.sub incl s) ∧ (books s).W.k=(V (WilsonMeasuredSignedActionOwnedBook.sub incl s)).k ∧
                HEq (books s).W (V (WilsonMeasuredSignedActionOwnedBook.sub incl s)) ∧ ∀i:Fin (D+1),(books s).V i=atRadius l cap V J₀ s.val i) ∧
              Licensed F (I:=I) Γ D t books J ∧ Licensed F (I:=I) Γ D t books Jc

include W₀ in
theorem original (simple:G.Simple)(run:WilsonViewerElectedHierarchy.Selected.{u} F almanac reader J₀ H arch l simple cohort)
    (slow:WilsonWindowReportingPace.Slow R.kit)(wide:∀j,1≤(R.family.path.levels.budget j).supportExponent)
    (located:∀s:Ioc (0:ℝ) radius,(s:ℝ)=Station.gap R.family.path.levels
      (b (grade (station s)) 0+offset s) (station s))
    (large:∀D:ℕ,∃ε>(0:ℝ),∀s:Ioc (0:ℝ) radius,(s:ℝ)<ε→D≤grade (station s))
    (school:WilsonPhysicalStationMixedWickCalibrated.Filed.{u} R B O χ (l:=l) H (arch:=arch) price count tests F J₀ b c P grade station offset book lo hi ax counted more almanac reader cohort simple):
    Served.{u} R B O χ (l:=l) H (arch:=arch) price count tests F J₀ b c P grade station offset book lo hi ax counted more almanac reader cohort simple:=by
  obtain ⟨δ,pos,incl,X,named,held,J,lead,near,duty,staff,neighbors,hears,Jc,change,joint,receipt,selected⟩:=school
  let cap(s:Ioc (0:ℝ) δ):=grade (station (lift incl s))
  let V:=home R b c grade station offset incl X
  have position(s:Ioc (0:ℝ) δ):(V s).wheel.r=s.val:=(located (lift incl s)).symm
  have calendar(xs:ℕ→Ioc (0:ℝ) δ)(vanish:Tendsto (fun i=>(xs i).val) atTop (𝓝 0)):
      Tendsto (fun i=>cap (xs i)) atTop atTop ∧ Tendsto (fun i=>(V (xs i)).k) atTop atTop:=
    dates grade station (fun i=>lift incl (xs i)) vanish large
  have owned:=WilsonMeasuredSignedActionOwnedIncome.original F simple run.bliss pos cap V J₀ J position
    (fun s=>(named s).1.choose) calendar staff
  obtain ⟨T',φ,a,d,e,same,scheme,comparison⟩:=receipt
  refine ⟨δ,pos,incl,X,named,held,J,lead,near,duty,staff,neighbors,hears,Jc,change,joint,
    ⟨T',φ,a,d,e,same,scheme,comparison⟩,selected,owned,?_,?_⟩
  · exact WilsonMeasuredSignedActionPosed.original F cap V J₀ J Jc owned same comparison
  · intro I _ _ _ base Γ D
    exact WilsonMeasuredSignedActionPosedSchool.original (I:=I) F W₀ simple run.bliss slow Γ wide cap V J₀ J Jc
      owned same comparison D

end YM.Integration.WilsonPhysicalStationMixedWickAction
end
