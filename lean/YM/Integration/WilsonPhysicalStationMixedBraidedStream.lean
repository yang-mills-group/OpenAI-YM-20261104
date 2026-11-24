import YM.Integration.WilsonPhysicalStationMixedSeatedStream
import YM.Integration.WilsonPhysicalStationMixedBraidedGeometry
import YM.Integration.WilsonPhysicalStationMixedWickNeighbors
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedBraidedStream
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
theorem original (i:ℕ)(rise:hi i=lo i+1)(simple:G.Simple)(below:(ℓ:Filter _) ≤ f.fuse)
    (width:∀ᶠk:ℕ in atTop,MergeProof.East.topL R.family.path.levels k ≤ R.family.path.levels.clock.monitor k)
    (located:∀s,(V s).wheel.r=(s:ℝ))
    (adjacent:∀s u:Ioc (0:ℝ) radius,(s:ℝ) ≤ u→(u:ℝ) ≤ 2*(s:ℝ)→
      (V u).k ≤ (V s).k ∧ (V s).k ≤ (V u).k+1)
    (comparable:∀n,(outer n:ℝ) ≤ 2*(inner n:ℝ))
    (registered:WilsonPhysicalStationOwnedTablePair.Held R F (l:=ℓ) J₀ H (arch:=arch) number tests cap V outer inner c J)
    (fund:Admitted R (f:=f) (l:=ℓ) J₀ H bind O ρ cost cap V pan outer inner (quantity R lo hi cnt)
      (ledger R (S:=S) book lo hi ax cnt more) c J):
    ∃start:ℕ,∃seats:∀n:ℕ,start ≤ n→Seat R (l:=ℓ) H F J₀ c.report J rise n,
      ∀q:ℕ,∀u:(standard R.family).Field (hi i),Pure R q u→∀ε:ℝ,0<ε→
      ∀ᶠ n:ℕ in atTop,∀earlier:start ≤ n,
        Result R F J c.report book lo hi ax i (show lo i ≤ hi i by omega) n q u (seats n earlier).g ε:=by

  have faculty {h:ℕ} (step:h=lo i+1):Faculty R (l:=ℓ) H number tests F J₀ c.report J step:=by
    subst h
    exact registered.2.2.2.2 (lo i)
  obtain ⟨held,dates,_,deep,_⟩:=fund false
  have geometry (n:ℕ):=WilsonPhysicalStationMixedBraidedGeometry.original R cap V outer inner c located adjacent comparable n (hi i)
  apply WilsonPhysicalStationMixedSeatedStream.original R F J₀ J c.report book lo hi ax i number tests
    simple below rise (faculty rise) bind O ρ cost cnt more (fun n=>cap (outer (c.pick n))) (fun n=>pan (outer (c.pick n)))
    (Filter.Eventually.of_forall held) dates deep width (fun n=>(geometry n).1) (fun n=>(geometry n).2.1)
  intro d
  obtain ⟨A,B,_,_,files⟩:=registered.2.2.2.1 d
  exact files.mono fun n pair=>⟨A,B,A,B,pair⟩
end YM.Integration.WilsonPhysicalStationMixedBraidedStream
end
