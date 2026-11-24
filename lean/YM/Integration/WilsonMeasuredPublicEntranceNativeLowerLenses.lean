import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerDated
import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerRadii
import YM.Integration.WilsonMeasuredPublicEntranceNativeParity
import YM.Integration.WilsonPhysicalStationMixedWickPaired
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerLenses
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

open WilsonPhysicalStationOwnedTableStanding (Seat)
open WilsonPhysicalStationMixedPortVoter (Pure)
open WilsonPhysicalStationMixedSeatedStream (Result)
def Tickets (i:ℕ)(rise:hi i=lo i+1):Prop:=
  ∃start:ℕ,∃seats:∀n:ℕ,start≤n→Seat R (l:=l) H F J₀ c.report J rise n,
    ∀q:ℕ,∀u:(standard R.family).Field (hi i),Pure R q u→∀ε:ℝ,0<ε→
      ∀ᶠn:ℕ in atTop,∀old:start≤n,Result R F J c.report book lo hi ax i (by omega) n q u (seats n old).g ε

theorem delivered (fallback:ℝ→tower S)(located:∀s,(V s).wheel.r=(s:ℝ))
    (owned:WilsonPhysicalStationOwnedTablePair.Held R F (l:=l) J₀ H (arch:=arch) number tests cap V outer inner c J)
    (read:WilsonPhysicalStationMixedWickPaired.Read R F cap V outer inner c J book lo hi ax)
    {r t:ℕ→ℝ}{s:ℝ}{shift:ℕ→ℕ}(schedule:Tendsto shift atTop atTop)(rate:Tendsto t atTop (𝓝 s))
    (places:∀n,(outer n:ℝ)=r (shift n) ∧ (inner n:ℝ)=t (shift n)*r (shift n))
    (i:ℕ)(rise:hi i=lo i+1)(tickets:Tickets R F (l:=l) J₀ H cap V outer inner c J book lo hi ax i rise)
    (src dst:(R.family.labels.level (hi i)).Index)(weight:((R.family.labels.level (hi i)).grades src).1=hi i):
    WilsonMeasuredPublicEntranceNativeLowerRefined.Refined R F atTop (atRadius l cap V fallback) r t s (hi i) src dst:=by
  obtain ⟨Y,bought⟩:=owned.1.meters
  obtain ⟨start,seats,sold⟩:=tickets
  apply WilsonMeasuredPublicEntranceNativeLowerDated.acquired R F J₀ J c.report book lo hi ax i rise start seats sold
    (atRadius l cap V fallback) (schedule.comp c.cofinal.tendsto_atTop) rate
  · intro n
    rw [even]
    exact (located _).trans (places (c.pick n)).1
  · intro n
    rw [odd]
    exact (located _).trans (places (c.pick n)).2
  · intro d
    filter_upwards [WilsonMeasuredPublicEntranceNativeParity.original l cap V fallback outer inner c bought d] with n hit
    simpa only [Function.comp_apply,(places (c.pick n)).1,(places (c.pick n)).2] using hit
  · exact (read false i).1
  · exact weight

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerLenses
end
