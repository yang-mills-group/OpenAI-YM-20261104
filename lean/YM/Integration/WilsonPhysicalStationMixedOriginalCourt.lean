import YM.Integration.WilsonPhysicalStationMixedEarnedCourt
import YM.Integration.WilsonPhysicalStationMixedWickChamberPorts
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedOriginalCourt
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
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}(J₀:ℝ→tower S)(J:Scaling S)
    (V:∀a,Vane R.family a){m k depth:ℕ}(book:Deck G)(lo hi:ℕ→ℕ)(ax:ℕ→Axis)(i:ℕ)
set_option quotPrecheck false
open WilsonPhysicalStationMixedWickChamberPorts (contact quantity ledger booked)
open WilsonPhysicalStationMixedWickCollege (chosen)
open WilsonPhysicalStationMixedHomogeneousCash (wallet earlier)
open WilsonPhysicalStationMixedPortVoter (Pure)
open WilsonPhysicalStationLowerReceiver (ear)
open WilsonPhysicalStationMixedOwnedSensor (scale)
local notation "h₀"=>hi i
local notation "e₀"=>lo i
local notation "room₀"=>chosen R (S:=S) book (e₀) (ax i)
variable (hm:(hi i) ≤ m)(hk:(hi i) ≤ k)(ca:(V m).checked f H m)(cb:(V k).checked f H k)(eh:(lo i) ≤ (hi i))
    (b:(R.family.labels.level ((hi i))).Index)(turn:Signed)(side:Fin 2)
    {w:Head R.family ((hi i))→(ℕ×ℕ)→R.family.label ((hi i))}{v:Head R.family ((hi i))→R.family.label ((hi i))}{g:ℝ}
    (owner:WilsonPhysicalStationBasisOwners.Earned R F (ℓ:=ℓ) J₀ J V hm hk ca cb eh w v g)(q:ℕ)
local notation "s₀"=>contact R (S:=S) book lo hi ax i true true b turn side
local notation "C₀"=>standard R.family
local notation "θ"=>R.family.path.levels.clock.monitor (V m).k
local notation "ax₀"=>R.family.path.levels
local notation "M₀"=>mag (ax₀) (V m).b (V m).k
local notation "M₁"=>mag (ax₀) (V k).b (V k).k
local notation "q₁"=>rank R.family (h₀) b
local notation "peer₁"=>probe R.family b turn side
local notation "position"=>tested (ax₀) (V m).b (V m).k (room₀).ξ
local notation "χ₀"=>scale R V (m:=m) (k:=k) g (h₀) q
include owner v b turn side in
theorem original (bind:Binding R.family)(O:HaarBudget G)(ρ:ChartRatio G)(cost:ℕ→ℝ)(cnt:ℕ→ℕ)
    (more:∀D,Fin (cnt D)→Slot R.family)(P:Tapes.Panel depth)
    (house:WilsonMovingForkReporterMixedHouses.Held (f:=f) R bind O ρ H cost
      (quantity R lo hi cnt) (ledger R (S:=S) book lo hi ax cnt more) P (V m))
    (active:i < depth+1)(admit:100*(max (h₀) (e₀)+1) ≤ depth)
    (dates:(V k).k=(V m).k ∨ (V k).k=(V m).k+1)(warm:WilsonPhysicalStationBasisClock.Live R (V m).k)
    (win:aperture R (V m).k (V k).k (h₀) (M₀) (M₁) ≤ 1)
    (inside:position∈(room₀).site)(fits:FitSky (ax₀) (V m).b (V m).k (room₀).ξ)
    {ak bk aa ba ae be:ℝ}
    (fine:Filed (f:=f) (l:=ℓ) J₀ J V (h₀) k ak bk)(leftA:Filed (f:=f) (l:=ℓ) J₀ J V (h₀) m aa ba)
    (lowerA:Filed (f:=f) (l:=ℓ) J₀ J V (e₀) m ae be)(simple:G.Simple)(below:(ℓ:Filter _)≤f.fuse)
    (wide:0 < (V m).wheel.r)(small:0 ≤ (V k).wheel.r)(order:(V k).wheel.r ≤ (V m).wheel.r)
    (big:1 ≤ θ)(u:(C₀).Field (h₀))(pure:Pure R q u):
    earlier R (S:=S) v u ∈ LinearMap.range (F.sector.derivatives.rise eh) ∧
    (‖ear R (S:=S) ((V m).wheel.r • position) (J.U m (h₀) peer₁)
      ((J.U k (h₀) u-χ₀ • J.U m (h₀) u)-earlier R (S:=S) v u)‖*θ^q₁ ≤
        θ^q*WilsonPhysicalStationMixedPortAllowance.fee R (s₀) u q depth (V m).k) ∧
    ∀j:Glyph book (e₀),‖ear R (S:=S) ((V m).wheel.r • position) (J.U m (e₀) (named R book (e₀) j))
      ((J.U k (h₀) u-χ₀ • J.U m (h₀) u)-earlier R (S:=S) v u)‖*θ^j.2.1.val ≤
      θ^q*WilsonPhysicalStationMixedCourtFare.lower R book (e₀) (room₀).site (room₀).compact (room₀).clear u q j depth (V m).k:=by
  refine ⟨WilsonPhysicalStationMixedHomogeneousCash.member R F v eh (fun a=>(owner.lower a).2) u,?_⟩
  let index:Fin (depth+1):=⟨i,active⟩
  obtain ⟨pick,hp⟩:=booked R (S:=S) book lo hi ax cnt more depth index true true b turn side
  have registered (a:(R.family.labels.level (e₀)).Index):∃j,ledger R (S:=S) book lo hi ax cnt more depth j=
      WilsonPhysicalStationMixedSchurNamed.slot R (e₀) (room₀).site (room₀).compact (room₀).clear (h₀) a:=
    booked R (S:=S) book lo hi ax cnt more depth index true false a 1 0
  choose pegs listed using registered
  exact WilsonPhysicalStationMixedEarnedCourt.original R F J₀ J V hm hk ca cb eh (s₀) (Nat.lt_succ_of_le hm)
    owner q (room₀).ξ book (Nat.lt_succ_of_le (eh.trans hm)) (room₀).site (room₀).compact (room₀).clear
    bind O ρ cost (quantity R lo hi cnt) (ledger R (S:=S) book lo hi ax cnt more) P house pick hp
    (by simpa [contact,WilsonPhysicalStationMixedWickChamberPorts.grade,max_eq_left eh] using admit)
    pegs listed admit dates warm win inside inside fits fine leftA leftA lowerA simple below wide small order big u pure
end YM.Integration.WilsonPhysicalStationMixedOriginalCourt
end
