import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerCourts
import YM.Integration.WilsonPhysicalStationMixedOriginalFare
import YM.Integration.WilsonPhysicalStationMixedWickAttendance
import YM.Integration.WilsonPhysicalStationOwnedTableFaculty
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedSeatedStream
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
def Result (le:lo i ≤ hi i)(n:ℕ)(q:ℕ)(u:(standard R.family).Field (hi i))(g ε:ℝ):Prop:=
  let m:=2*n
  let k:=2*n+1
  let x:=(V m).wheel.r • tested AX (V m).b (V m).k (room₀).ξ
  ∀(b:(R.family.labels.level (hi i)).Index)(turn:Signed)(side:Fin 2),
    Meter R F book (lo i) (ax i) le (J.U m) x q (rank R.family (hi i) b)
      (ear R x (J.U m (hi i) (probe R.family b turn side)))
      (J.U k (hi i) u-scale R V (m:=m) (k:=k) g (hi i) q • J.U m (hi i) u) ε
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
    (files:∀d,∀ᶠn:ℕ in atTop,∃A B C E:ℝ,Filed (f:=f) (l:=ℓ) J₀ J V d (2*n) A B ∧ Filed (f:=f) (l:=ℓ) J₀ J V d (2*n+1) C E):
    ∃start:ℕ,∃seats:∀n:ℕ,start ≤ n→Seat R (l:=ℓ) H F J₀ V J rise n,
    ∀q:ℕ,∀u:(standard R.family).Field (hi i),Pure R q u→∀ε:ℝ,0<ε→
      ∀ᶠ n:ℕ in atTop,∀earlier:start ≤ n,
        Result R F J V book lo hi ax i (show lo i ≤ hi i by omega) n q u (seats n earlier).g ε:=by
  obtain ⟨start,seats,_⟩:=faculty
  refine ⟨start,seats,?_⟩
  intro q u pure ε positive
  let size:=100*(max (hi i) (lo i)+1)
  let wanted:=max i (max (room₀).floor size)
  obtain ⟨_,calendar⟩:=WilsonPhysicalStationMixedWickAttendance.original R bind O ρ cost (quantity R lo hi cnt)
    (ledger R (S:=S) book lo hi ax cnt more) P (fun n=>V (2*n)) held late deep simple
    (room₀).ξ (room₀).generic (room₀).site (room₀).neighborhood wanted
  have fees:=WilsonPhysicalStationMixedOriginalFare.original R (S:=S) book lo hi ax i u q simple deep late positive
  have warm:=late.eventually (WilsonPhysicalStationBasisClock.original R simple width)
  filter_upwards [fees,calendar,warm,files (hi i),files (lo i)] with n prices paid hot fresh lower
  intro earlier b turn side
  let Y:=seats n earlier
  obtain ⟨house,big,enough,wide,inside,fit⟩:=paid
  obtain ⟨X,C,X',C',upperA,upperB⟩:=fresh
  obtain ⟨L,B,L',B',lowerA,_⟩:=lower
  let A:=V (2*n)
  let B₁:=V (2*n+1)
  have fraction:B₁.wheel.r/A.wheel.r ≤ 1:=(div_le_one A.wheel.rad).2 (near n)
  have win:aperture R A.k B₁.k (hi i) (mag (AX) A.b A.k) (mag (AX) B₁.b B₁.k) ≤ 1:=
    pow_le_one₀ (div_nonneg B₁.wheel.rad.le A.wheel.rad.le) fraction
  have started:i<D n+1:=Nat.lt_succ_of_le ((le_max_left ..).trans enough)
  have wideEnough:size ≤ D n:=(le_max_right ..).trans ((le_max_right ..).trans enough)
  have floor:(room₀).floor ≤ D n:=(le_max_left ..).trans ((le_max_right ..).trans enough)
  have meter:=WilsonMeasuredPublicEntranceNativeLowerCourts.original R F J₀ J V book lo hi ax i
    Y.da Y.db Y.ca Y.cb (show lo i ≤ hi i by omega) b turn side Y.earned q bind O ρ cost cnt more (P n)
    house started wideEnough (ages n) hot win inside fit upperB upperA lowerA simple below wide B₁.wheel.rad.le
    (near n) big u pure floor
  obtain ⟨T,W,eps,fee,cap,nonnegative,earned,amount⟩:=meter
  exact ⟨T,W,eps,fee,cap,nonnegative,earned,amount.trans (prices b turn side).le⟩
end YM.Integration.WilsonPhysicalStationMixedSeatedStream
end
