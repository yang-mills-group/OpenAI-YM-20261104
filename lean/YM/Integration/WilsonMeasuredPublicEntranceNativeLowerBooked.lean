import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerLenses
import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerUniform
import YM.Integration.WilsonPhysicalStationMixedEnrolledStream
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerBooked
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


open PhysicalNext.Repeat Lotus MergeProof PhysicalNext.Repeat.Legato Bandage Campaign
open Next.Foundations OPE Work.G08
open WilsonMovingForkReporterFixedRanks (Axes)
open WilsonMovingForkReporterRankTables (Named)
open WilsonMovingForkReporterBasisVisits (Seen)
open WilsonMovingForkReporterBothArms (Filed)
open WilsonMovingForkReporterRestriction (vane)
open WilsonMeasuredPublicEntranceNativeFrame (atRadius)
open WilsonPhysicalStationOwnedTableFaculty (Faculty)
variable {G:Gauge}(R:Run G){T:Campaign R}(L:Pillars R T){f:Extraction.Order}{S:Table R.family.book}
    (fac:Facilities R.family f S)(F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}
    (J₀:ℝ→tower S)(H:(Bel R.family.book).Hierarchy){arch:Arch R.family}
    (B:Binding R.family)(O:HaarBudget G)(χ:ChartRatio G)(price:ℕ→ℝ)
variable (number:ℕ→ℕ)(tests:∀d,Fin (number d)→Axes R.family)
    {radius:ℝ}(cap:Ioc (0:ℝ) radius→ℕ)(V:∀s,Vane R.family (cap s))
    (pan:∀s,Tapes.Panel (cap s))(outer inner:ℕ→Ioc (0:ℝ) radius)
open MS MS.Land MS.Menus MS.Theater XSpace.Structure1 Local.Physical
open WilsonMovingForkReporterMixedBasis (Slot)
open WilsonPhysicalStationMixedWickNeighbors (month venue Admitted)
open WilsonPhysicalStationMixedWickCofinal (Paid)
open WilsonPhysicalStationMixedWickChamberPorts (quantity ledger)
open WilsonPhysicalStationMixedWickCollege (chosen)
variable (c:Pair (fun i=>V (outer i)) (fun i=>V (inner i)))(J:Scaling S)
    (book:Deck G)(lo hi:ℕ→ℕ)(ax:ℕ→Axis)(counted:ℕ→ℕ)(more:∀d,Fin (counted d)→Slot R.family)
local notation "M₀" => ledger R (S:=S) book lo hi ax counted more
local notation "AX" => R.family.path.levels

open WilsonPhysicalStationMixedEnrolledStream (Listening)
open WilsonMeasuredPublicEntranceNativeLowerUniform (Offered)

theorem original (fallback:ℝ→tower S)(small:0<radius)(located:∀s,(V s).wheel.r=(s:ℝ))
    (rooms:∀e:ℕ,∃i,lo i=e ∧ hi i=e+1)
    (paid:Listening R F (ℓ:=l) (H:=H) (arch:=arch) J₀ B O χ price number tests cap V pan book lo hi ax counted more)
    (d:ℕ):Offered R F (atRadius l cap V fallback) d:=by
  intro r t s _ near ratio positive band apart
  obtain ⟨shift,cofinal,o,u,places,left,right,separate,compare⟩:=
    WilsonMeasuredPublicEntranceNativeLowerRadii.original small near ratio positive band apart
  obtain ⟨w,charts,registered,_,read,_,heard⟩:=paid o u left right separate compare
  intro h great _
  cases h with
  | zero=>omega
  | succ e=>
    obtain ⟨i,base,high⟩:=rooms e
    have rise:hi i=lo i+1:=by omega
    have funded:=WilsonMeasuredPublicEntranceNativeLowerLenses.delivered R F J₀ H number tests cap V o u w charts book lo hi ax
      fallback located registered read cofinal ratio places i rise (heard i rise)
    rw [high] at funded
    dsimp only
    exact fun a b ha _ _=>funded a b ha

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerBooked
end
