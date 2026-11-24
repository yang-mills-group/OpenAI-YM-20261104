import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerFiledPort
import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerReached
import YM.Integration.WilsonPhysicalStationMixedSeatedStream
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerDated
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
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}(J₀:ℝ→tower S)(J:Scaling S)
    (V:∀a,Vane R.family a)(book:Deck G)(lo hi:ℕ→ℕ)(ax:ℕ→Axis)(i:ℕ)
local notation "room₀" => chosen R (S:=S) book (lo i) (ax i)
local notation "AX"=>R.family.path.levels
theorem acquired (rise:hi i=lo i+1)(start:ℕ)(seats:∀n:ℕ,start≤n→Seat R (l:=ℓ) H F J₀ V J rise n)
    (market:∀q:ℕ,∀u:(standard R.family).Field (hi i),Pure R q u→∀ε:ℝ,0<ε→
      ∀ᶠn:ℕ in atTop,∀old:start≤n,WilsonPhysicalStationMixedSeatedStream.Result R F J V book lo hi ax i (by omega) n q u (seats n old).g ε)
    (legacy:ℝ→tower S){r t:ℕ→ℝ}{s:ℝ}{pick:ℕ→ℕ}(cofinal:Tendsto pick atTop atTop)(ratio:Tendsto t atTop (𝓝 s))
    (outer:∀n,(V (2*n)).wheel.r=r (pick n))(inner:∀n,(V (2*n+1)).wheel.r=t (pick n)*r (pick n))
    (posted:∀d,∀ᶠn:ℕ in atTop,legacy (r (pick n)) d=J.U (2*n) d ∧ legacy (t (pick n)*r (pick n)) d=J.U (2*n+1) d)
    (centers:Tendsto (fun n=>tested AX (V (2*n)).b (V (2*n)).k (room₀).ξ) atTop (𝓝 (room₀).ξ))
    (src dst:(R.family.labels.level (hi i)).Index)(weight:((R.family.labels.level (hi i)).grades src).1=hi i):
    WilsonMeasuredPublicEntranceNativeLowerRefined.Refined R F atTop legacy r t s (hi i) src dst:=by
  let g (n:ℕ):=if old:start≤n then (seats n old).g else 1
  let q:=((R.family.labels.level (hi i)).grades src).2
  let u:=(standard R.family).project (hi i) (Pi.single src 1)
  have source:Pure R q u:=WilsonPhysicalStationMixedPortVoter.named R (⟨src,weight⟩:WilsonPhysicalStationFullVote.Head R.family (hi i))
  have range:∀ᶠn:ℕ in atTop,1/8≤g n ∧ g n≤12:=(eventually_ge_atTop start).mono fun n old=>by
    simpa only [g,dif_pos old] using (seats n old).earned.bracket
  apply WilsonMeasuredPublicEntranceNativeLowerReached.original R F book (lo i) (ax i) src dst room₀
    (by omega) (by omega) cofinal ratio range centers
  dsimp only
  intro b same tol positive
  filter_upwards [eventually_ge_atTop start,market q u source tol positive,posted (lo i),posted (hi i)] with n old sale low high
  have paid:=sale old b 1 0
  have rp:0<r (pick n):=outer n ▸ (V (2*n)).wheel.rad
  have label:rank R.family (hi i) b=((R.family.labels.level (hi i)).grades dst).2:=same
  apply WilsonMeasuredPublicEntranceNativeLowerGauge.filed R F book (lo i) (ax i) (by omega) legacy (r (pick n)) (t (pick n)) _ (J.U (2*n)) (J.U (2*n+1))
    low.1 high.1 high.2 _ _ _ _ tol
  simpa only [WilsonPhysicalStationMixedNamedProbe.neutral,WilsonPhysicalStationMixedOwnedSensor.scale,inner n,outer n,
    mul_div_cancel_right₀ (t (pick n)) rp.ne',label,g,dif_pos old] using paid

theorem original (number:ℕ→ℕ)(tests:∀D,Fin (number D)→Axes R.family)
    (simple:G.Simple)(below:(ℓ:Filter _) ≤ f.fuse)(rise:hi i=lo i+1)
    (faculty:Faculty R (l:=ℓ) H number tests F J₀ V J rise)
    (bind:Binding R.family)(O:HaarBudget G)(ρ:ChartRatio G)(cost:ℕ→ℝ)(cnt:ℕ→ℕ)
    (more:∀D,Fin (cnt D)→Slot R.family)(D:ℕ→ℕ)(P:∀n,Tapes.Panel (D n))
    (held:∀ᶠn:ℕ in atTop,WilsonMovingForkReporterMixedHouses.Held (f:=f) R bind O ρ H cost (quantity R lo hi cnt)
      (ledger R (S:=S) book lo hi ax cnt more) (P n) (V (2*n)))
    (late:Tendsto (fun n=>(V (2*n)).k) atTop atTop)(deep:Tendsto D atTop atTop)
    (width:∀ᶠk:ℕ in atTop,MergeProof.East.topL (AX) k ≤ (AX).clock.monitor k)
    (ages:∀n,(V (2*n+1)).k=(V (2*n)).k ∨ (V (2*n+1)).k=(V (2*n)).k+1)
    (near:∀n,(V (2*n+1)).wheel.r ≤ (V (2*n)).wheel.r)
    (files:∀d,∀ᶠn:ℕ in atTop,∃A B C E:ℝ,Filed (f:=f) (l:=ℓ) J₀ J V d (2*n) A B ∧ Filed (f:=f) (l:=ℓ) J₀ J V d (2*n+1) C E)
    (legacy:ℝ→tower S){r t:ℕ→ℝ}{s:ℝ}{pick:ℕ→ℕ}(cofinal:Tendsto pick atTop atTop)(ratio:Tendsto t atTop (𝓝 s))
    (outer:∀n,(V (2*n)).wheel.r=r (pick n))(inner:∀n,(V (2*n+1)).wheel.r=t (pick n)*r (pick n))
    (posted:∀d,∀ᶠn:ℕ in atTop,legacy (r (pick n)) d=J.U (2*n) d ∧ legacy (t (pick n)*r (pick n)) d=J.U (2*n+1) d)
    (centers:Tendsto (fun n=>tested AX (V (2*n)).b (V (2*n)).k (room₀).ξ) atTop (𝓝 (room₀).ξ))
    (src dst:(R.family.labels.level (hi i)).Index)(weight:((R.family.labels.level (hi i)).grades src).1=hi i):
    WilsonMeasuredPublicEntranceNativeLowerRefined.Refined R F atTop legacy r t s (hi i) src dst:=by
  obtain ⟨start,seats,market⟩:=WilsonPhysicalStationMixedSeatedStream.original R F J₀ J V book lo hi ax i number tests simple
    below rise faculty bind O ρ cost cnt more D P held late deep width ages near files
  exact acquired R F J₀ J V book lo hi ax i rise start seats market legacy cofinal ratio outer inner posted centers src dst weight

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerDated
end
