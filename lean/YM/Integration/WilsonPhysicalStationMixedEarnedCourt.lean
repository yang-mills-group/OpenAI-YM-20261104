import YM.Integration.WilsonPhysicalStationMixedEarnedEar
import YM.Integration.WilsonPhysicalStationMixedCourtFare
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedEarnedCourt
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
    (V:∀i,Vane R.family i){m k h e depth:ℕ}(hm:h ≤ m)(hk:h ≤ k)
    (ca:(V m).checked f H m)(cb:(V k).checked f H k)(eh:e ≤ h)
    (s:Slot R.family)(dr:s.right < m+1)
    {w:Head R.family h→(ℕ×ℕ)→R.family.label h}{v:Head R.family h→R.family.label h}{g:ℝ}
    (owner:WilsonPhysicalStationBasisOwners.Earned R F (ℓ:=ℓ) J₀ J V hm hk ca cb eh w v g)
    (q:ℕ)(ξ:Points 2)
    (book:Deck G)(he:e < m+1)(domain:Set (Points 2))(compact:IsCompact domain)(clear:domain⊆conf 2)
set_option quotPrecheck false
open WilsonPhysicalStationMixedHomogeneousCash (wallet earlier)
open WilsonPhysicalStationMixedPortVoter (Pure)
open WilsonPhysicalStationMixedFixedSensor (tip)
open WilsonPhysicalStationLowerReceiver (ear)
local notation "C₀"=>standard R.family
local notation "θ"=>R.family.path.levels.clock.monitor (V m).k
local notation "ax₀"=>R.family.path.levels
local notation "M₀"=>mag (ax₀) (V m).b (V m).k
local notation "M₁"=>mag (ax₀) (V k).b (V k).k
local notation "q₁"=>rank R.family s.right s.dual
local notation "peer₁"=>probe R.family s.dual s.turn s.arm
local notation "r₁"=>(⟨s.right,dr⟩:Fin (m+1))
local notation "position"=>tested (ax₀) (V m).b (V m).k ξ
open WilsonPhysicalStationMixedOwnedSensor (scale)
local notation "χ₀"=>scale R V (m:=m) (k:=k) g h q
local notation "seat₀"=>WilsonPhysicalStationMixedSchurNamed.slot R e domain compact clear h
local notation "earlier₀" => earlier R (S:=S) v
include owner dr he in
theorem original (bind:Binding R.family)(O:HaarBudget G)(ρ:ChartRatio G)(price:ℕ→ℝ)(qty:ℕ→ℕ)
    (menu:∀D,Fin (qty D)→Slot R.family)(P:Tapes.Panel depth)
    (house:WilsonMovingForkReporterMixedHouses.Held (f:=f) R bind O ρ H price qty menu P (V m))
    (pick:Fin (qty depth))(record:menu depth pick=onLeft h s)
    (admit:100*(max h s.right+1) ≤ depth)
    (pegs:(R.family.labels.level e).Index→Fin (qty depth))(listed:∀b,menu depth (pegs b)=seat₀ b)
    (allow:100*(max h e+1) ≤ depth)
    (dates:(V k).k=(V m).k ∨ (V k).k=(V m).k+1)(warm:WilsonPhysicalStationBasisClock.Live R (V m).k)
    (win:aperture R (V m).k (V k).k h (M₀) (M₁) ≤ 1)
    (loc:position∈s.site)(inside:position∈domain)(fit:FitSky (ax₀) (V m).b (V m).k ξ)
    {ak bk aa ba ar br ae be:ℝ}
    (fine:Filed (f:=f) (l:=ℓ) J₀ J V h k ak bk)(leftA:Filed (f:=f) (l:=ℓ) J₀ J V h m aa ba)
    (rightA:Filed (f:=f) (l:=ℓ) J₀ J V s.right m ar br)(lowerA:Filed (f:=f) (l:=ℓ) J₀ J V e m ae be)(simple:G.Simple)(below:(ℓ:Filter _) ≤ f.fuse)
    (wide:0 < (V m).wheel.r)(small:0 ≤ (V k).wheel.r)(order:(V k).wheel.r ≤ (V m).wheel.r)
    (big:1 ≤ θ)(u:(C₀).Field h)(pure:Pure R q u):
    (‖ear R (S:=S) ((V m).wheel.r • position) (J.U m s.right peer₁)
      ((J.U k h u-χ₀ • J.U m h u)-earlier R (S:=S) v u)‖*θ^q₁ ≤
        θ^q*WilsonPhysicalStationMixedPortAllowance.fee R s u q depth (V m).k) ∧
      ∀j:Glyph book e,‖ear R (S:=S) ((V m).wheel.r • position) (J.U m e (named R book e j))
        ((J.U k h u-χ₀ • J.U m h u)-earlier₀ u)‖*θ^j.2.1.val ≤
        θ^q*WilsonPhysicalStationMixedCourtFare.lower R book e domain compact clear u q j depth (V m).k:=by
  constructor
  · exact WilsonPhysicalStationMixedEarnedEar.original R F J₀ J V hm hk ca cb eh s dr owner q ξ
      bind O ρ price qty menu P house pick record admit dates warm win loc fit fine leftA rightA simple below wide small order big u pure
  · intro j
    apply WilsonPhysicalStationMixedNativePorts.original R (J.U m) book e j _ _ _ q (zero_le_one.trans big)
    intro b
    exact WilsonPhysicalStationMixedEarnedEar.original R F J₀ J V hm hk ca cb eh (seat₀ b) he owner q ξ
      bind O ρ price qty menu P house (pegs b) (listed b) allow dates warm win inside fit fine leftA lowerA simple below wide small order big u pure
end YM.Integration.WilsonPhysicalStationMixedEarnedCourt
end
