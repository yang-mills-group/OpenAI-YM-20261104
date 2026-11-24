import YM.Integration.WilsonPhysicalStationMixedBraidedStream
import YM.Integration.WilsonPhysicalStationMixedWickPaired
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedEnrolledStream
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open Next.Rank Next.Rank.Station Next.Rank.Perch Next.Rank.Price
open Further.CorrectedLift (ladder)
open WilsonMovingForkReporterBothArms (Filed)
open WilsonOriginalBlissMixedGram (grades)
open WilsonPhysicalStationMixedWickPair (cell)
open WilsonPhysicalStationMixedWickTest (reference)
open WilsonMeasuredPublicEntranceOrderedPins (physical)
open scoped Topology Classical BigOperators
open WilsonPhysicalStationSubtractedPair (lower)
open WilsonPhysicalStationFullVote (Head Below)
open WilsonPhysicalStationPureReceipt (coefficients ballot left)
open WilsonPhysicalStationMixedListener (port value actual)
open WilsonPhysicalStationThermalStart (entered)
open WilsonPhysicalStationMixedBilledPort (base)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationKineticLimit (transit)
open WilsonPhysicalStationThermalBasisOffice (rank)
open WilsonPhysicalStationMixedCommittedBallot (signed)
open WilsonPhysicalStationMixedBallotCash (weighted)
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
    PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open WilsonMovingForkReporterMixedBasis (Slot)
open WilsonPhysicalStationMixedSchurBoard (onLeft Billed charge)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonPhysicalStationMeasuredCash (aperture)
open WilsonPhysicalStationMixedPostedMarket (Paid)
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramFreePanel (named)
open WilsonPhysicalStationMixedWickChamberPorts (quantity ledger)
open WilsonPhysicalStationMixedWickCollege (chosen)
open WilsonPhysicalStationOwnedTableStanding (Seat)
open WilsonPhysicalStationOwnedTableFaculty (Faculty)
open WilsonPhysicalStationMixedPortVoter (Pure)
open WilsonPhysicalStationLowerReceiver (ear)
open WilsonPhysicalStationMixedOwnedSensor (scale)
open WilsonMovingForkReporterFixedRanks (Axes)
open WilsonMeasuredPublicEntranceNativeLowerTolerance (Meter)
set_option quotPrecheck false
open WilsonMovingForkReporterBraided
open PhysicalNext.Repeat Lotus MergeProof PhysicalNext.Repeat.Legato Bandage Campaign
open WilsonPhysicalStationMixedWickPaired (Read)
open WilsonPhysicalStationMixedSeatedStream (Result)
open WilsonPhysicalStationMixedWickNeighbors (Admitted)
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{arch:Arch R.family}(J₀:ℝ→tower S)
    (bind:Binding R.family)(O:HaarBudget G)(ρ:ChartRatio G)(cost:ℕ→ℝ)
    (number:ℕ→ℕ)(tests:∀D,Fin (number D)→Axes R.family)
    {radius:ℝ}(cap:Ioc (0:ℝ) radius→ℕ)(V:∀s,Vane R.family (cap s))
    (pan:∀s,Tapes.Panel (cap s))(outer inner:ℕ→Ioc (0:ℝ) radius)
    (c:Pair (fun i=>V (outer i)) (fun i=>V (inner i)))(J:Scaling S)
    (book:Deck G)(lo hi:ℕ→ℕ)(ax:ℕ→Axis)(cnt:ℕ→ℕ)(more:∀D,Fin (cnt D)→Slot R.family)

def Heard :Prop:=
  ∀(i:ℕ)(rise:hi i=lo i+1),
    ∃start:ℕ,∃seats:∀n:ℕ,start ≤ n→Seat R (l:=ℓ) H F J₀ c.report J rise n,
      ∀q:ℕ,∀u:(standard R.family).Field (hi i),Pure R q u→∀ε:ℝ,0<ε→
      ∀ᶠ n:ℕ in atTop,∀earlier:start ≤ n,
        Result R F J c.report book lo hi ax i (show lo i ≤ hi i by omega) n q u (seats n earlier).g ε

local notation "M₀"=>ledger R (S:=S) book lo hi ax cnt more
def Listening :Prop:=
  ∀o u:ℕ→Ioc (0:ℝ) radius,Tendsto (fun i=>(o i:ℝ)) atTop (𝓝 0)→
    Tendsto (fun i=>(u i:ℝ)) atTop (𝓝 0)→(∀ᶠi:ℕ in atTop,(u i:ℝ)<(o i:ℝ))→
    (∀i,(o i:ℝ)≤2*(u i:ℝ))→∃w:Pair (fun i=>V (o i)) (fun i=>V (u i)),∃charts:Scaling S,
    WilsonPhysicalStationOwnedTablePair.Held R F (l:=ℓ) J₀ H (arch:=arch) number tests cap V o u w charts ∧
    Admitted R (f:=f) (l:=ℓ) J₀ H bind O ρ cost cap V pan o u (quantity R lo hi cnt) M₀ w charts ∧
    Read R F cap V o u w charts book lo hi ax ∧
    (∀n:ℕ,(w.report (2*n+1)).k=(w.report (2*n)).k ∨ (w.report (2*n+1)).k=(w.report (2*n)).k+1) ∧
    Heard R F (ℓ:=ℓ) (H:=H) J₀ cap V o u w charts book lo hi ax

theorem original (simple:G.Simple)(below:(ℓ:Filter _)≤f.fuse)
    (width:∀ᶠk:ℕ in atTop,MergeProof.East.topL R.family.path.levels k≤R.family.path.levels.clock.monitor k)
    (located:∀s,(V s).wheel.r=(s:ℝ))
    (adjacent:∀s u:Ioc (0:ℝ) radius,(s:ℝ)≤u→(u:ℝ)≤2*(s:ℝ)→
      (V u).k≤(V s).k ∧ (V s).k≤(V u).k+1)
    (school:WilsonPhysicalStationMixedWickPaired.Listening R F (l:=ℓ) J₀ H (arch:=arch) bind O ρ cost number tests cap V pan book lo hi ax cnt more):
    Listening R F (ℓ:=ℓ) (H:=H) (arch:=arch) J₀ bind O ρ cost number tests cap V pan book lo hi ax cnt more:=by
  intro o u left right apart compare
  obtain ⟨w,charts,first,fund,read⟩:=school o u left right apart compare
  refine ⟨w,charts,first,fund,read,fun n=>(WilsonPhysicalStationMixedBraidedGeometry.original R cap V o u w located adjacent compare n 0).1,?_⟩
  intro i rise
  exact WilsonPhysicalStationMixedBraidedStream.original R F J₀ bind O ρ cost number tests cap V pan o u w charts book lo hi ax cnt more i rise simple below width located adjacent compare first fund

end YM.Integration.WilsonPhysicalStationMixedEnrolledStream
end
