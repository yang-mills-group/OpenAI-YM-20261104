import YM.Integration.WilsonPhysicalStationMixedWickFundedBooks
import YM.Integration.WilsonOriginalObservedRoseBornOwnedCourse

/-! The priced book of the two calibrated frames supplies the original (6,4,4) thermal measurement. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
universe u
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickRose
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
variable {axis₀:Axis}{ε₀:ℝ}{schedule:WilsonOriginalAllOrderCourse.Schedule G}
def Measured (simple:G.Simple)(paid:WilsonOriginalAllOrderCourse.Paid.{u} axis₀ simple ε₀ (WilsonOriginalOpticalSchedule.prepared schedule) R T₀ W₀):Prop:=
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
          ∃selected:WilsonViewerElectedHierarchy.Selected.{u} F almanac reader Jc H arch l simple cohort,
          WilsonPhysicalStationMixedEnrolledStream.Listening R F (ℓ:=l) (H:=H) (arch:=arch) J B O χ price count tests cap V
            (fun s=>P (cap s) (offset (lift sub s)) 0) book lo hi ax counted more ∧
          (∀d:ℕ,∀a:ℝ,0<a→WilsonPhysicalPositionHalfRange.uniform J d a) ∧
          (∀d:ℕ,∀a:ℝ,0<a→WilsonPhysicalPositionHalfRange.uniform Jc d a) ∧
          WilsonPhysicalStationMixedWickReposed.FiniteRows R J Jc ∧ Coupling G (wilson arch) ∧
          WilsonPositionScaleLawUniformIncome.Bought F Jc simple (Y:=l) H (arch:=arch) ∧
          Issued F (H:=H) (l:=l) (z:=arch) cap V J₀ J ∧
          Issued F (H:=H) (l:=l) (z:=arch) cap V J₀ Jc ∧
          (∀(I:Type)[Fintype I][DecidableEq I][Nonempty I](base:ℕ)
            (Γ:WilsonViewerReportingGrid.Grid (ℓ:=l) F base (wilson arch))(D:ℕ),
            ∃t:ℕ,∃ε:ℝ,0<ε ∧ ∃incl:ε≤δ,∃books:(s:{s:ℝ // 0<s ∧ s<ε})→Book F (l:=l) H arch D t s.val,
              (∀s,(books s).k=cap (WilsonMeasuredSignedActionOwnedBook.sub incl s) ∧ (books s).W.k=(V (WilsonMeasuredSignedActionOwnedBook.sub incl s)).k ∧
                HEq (books s).W (V (WilsonMeasuredSignedActionOwnedBook.sub incl s)) ∧ ∀i:Fin (D+1),(books s).V i=atRadius l cap V J₀ s.val i) ∧
              (∀s,WilsonMovingForkWindowBooks.Priced F (books s)) ∧
              Licensed F (I:=I) Γ D t books J ∧ Licensed F (I:=I) Γ D t books Jc) ∧
          ∀(I:Type)[Fintype I][DecidableEq I][Nonempty I](base:ℕ)
            (Γ:WilsonViewerReportingGrid.Grid (ℓ:=l) F base (wilson arch)),
            ∃t:ℕ,∃(ε:ℝ)(ep:0<ε), ∃incl:ε≤δ,∃books:(s:{s:ℝ // 0<s ∧ s<ε})→Book F (l:=l) H arch 6 t s.val,
              (∀s,(books s).k=cap (WilsonMeasuredSignedActionOwnedBook.sub incl s) ∧ (books s).W.k=(V (WilsonMeasuredSignedActionOwnedBook.sub incl s)).k ∧
                HEq (books s).W (V (WilsonMeasuredSignedActionOwnedBook.sub incl s)) ∧ ∀i:Fin 7,(books s).V i=atRadius l cap V J₀ s.val i) ∧
              ∃priceBook:∀s,WilsonMovingForkWindowBooks.Priced F (books s),
              Licensed F (I:=I) Γ 6 t books J ∧ Licensed F (I:=I) Γ 6 t books Jc ∧
              ∀(Z:WilsonPrescription G)(n:ℕ)(hp:0<n)(ratio:Z.run.ratio=(3:ℕ)^n)(stage:ℕ)
                (color:G.ColorIndex)(paths:FundedOriginalVacuumPaths.prices R.kit),
                type_of% (WilsonOriginalObservedRoseBornOwnedCourse.original paid F Jc selected.bliss selected.leading
                  selected.obeys Z hp ratio stage color paths t ep books priceBook)

theorem original (simple:G.Simple)(paid:WilsonOriginalAllOrderCourse.Paid.{u} axis₀ simple ε₀ (WilsonOriginalOpticalSchedule.prepared schedule) R T₀ W₀)
    (stock:WilsonPhysicalStationMixedWickFundedBooks.Funded.{u} R B O χ (l:=l) H (arch:=arch) price count tests F J₀ b c P grade station offset book lo hi ax counted more almanac reader cohort simple):
    Measured.{u} R B O χ (l:=l) H (arch:=arch) price count tests F J₀ b c P grade station offset book lo hi ax counted more almanac reader cohort W₀ simple paid:=by
  obtain ⟨δ,pos,incl,X,named,held,J,leading,near,duty,staff,neighbors,listening,Jc,change,joint,receipt,selected,stream,range,calibrated,rows,heat,scale,unposed,posed,books⟩:=stock
  refine ⟨δ,pos,incl,X,named,held,J,leading,near,duty,staff,neighbors,listening,Jc,change,joint,receipt,selected,stream,range,calibrated,rows,heat,scale,unposed,posed,books,?_⟩
  intro I _ _ _ base Γ
  obtain ⟨t,ε,ep,small,B₆,owned,priced,first,second⟩:=books I base Γ 6
  refine ⟨t,ε,ep,small,B₆,owned,priced,first,second,?_⟩
  intro Z n hp ratio stage color paths
  exact WilsonOriginalObservedRoseBornOwnedCourse.original paid F Jc selected.bliss selected.leading selected.obeys
    Z hp ratio stage color paths t ep B₆ priced
end YM.Integration.WilsonPhysicalStationMixedWickRose
end
