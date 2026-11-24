import YM.Integration.WilsonPhysicalStationMixedPostedMarket
import YM.Integration.WilsonPhysicalStationMixedSchurBoard
import YM.Integration.WilsonPhysicalStationBasisOwners
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedPurchasedMarket
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
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}(J₀:ℝ→tower S)(J:Scaling S)
    (V:∀i,Vane R.family i){m k h e depth:ℕ}(hm:h ≤ m)(hk:h ≤ k)
    (ca:(V m).checked f H m)(cb:(V k).checked f H k)(eh:e ≤ h)
    {I:Type*}[Fintype I](s:I→Slot R.family)(dr:∀i,(s i).right < m+1)
    {w:Head R.family h→(ℕ×ℕ)→R.family.label h}{v:Head R.family h→R.family.label h}{g:ℝ}
    (owner:WilsonPhysicalStationBasisOwners.Earned R F (ℓ:=ℓ) J₀ J V hm hk ca cb eh w v g)
    (q Q:ℕ)(η:I→ℂ)(roof:I→ℝ)(x:I→Points 2)
set_option quotPrecheck false
local notation "θ"=>R.family.path.levels.clock.monitor (V m).k
local notation "grade" => (fun i=>(⟨(s i).right,dr i⟩:Fin (m+1)))
local notation "peer" => (fun i=>probe R.family (s i).dual (s i).turn (s i).arm)
local notation "ax₀"=>R.family.path.levels
local notation "M₀"=>mag (ax₀) (V m).b (V m).k
local notation "M₁"=>mag (ax₀) (V k).b (V k).k

include owner in
theorem filed (market:Billed R (V m) (V k) (Nat.lt_succ_of_le hm) (Nat.lt_succ_of_le hk) ca cb s dr e depth)
    (loc:∀i,tested (ax₀) (V m).b (V m).k (x i)∈(s i).site)(fit:∀i,FitSky (ax₀) (V m).b (V m).k (x i))
    (pos:∀i,0 ≤ roof i)(wage:∀i,‖η i‖*(θ)^Q ≤ roof i*(θ)^(rank R.family (s i).right (s i).dual)):
    Paid R V hk cb q Q w (grade) (peer) η x (∑i,roof i*WilsonPhysicalStationMixedSchurBoard.charge R (V m) s (h:=h) i depth q (x i)):=by
  filter_upwards [market] with N funded per top a homogeneous
  have bill:=funded per top a.val (w a (N,per)) (owner.chart a (N,per) top) x loc fit Q η roof pos wage
  dsimp only at bill
  rw [homogeneous] at bill
  exact bill

include owner in
theorem original (bind:Binding R.family)(O:HaarBudget G)(ρ:ChartRatio G)(price:ℕ→ℝ)(qty:ℕ→ℕ)
    (menu:∀D,Fin (qty D)→Slot R.family)(P:Tapes.Panel depth)
    (house:WilsonMovingForkReporterMixedHouses.Held (f:=f) R bind O ρ H price qty menu P (V m))
    (pick:I→Fin (qty depth))(record:∀i,menu depth (pick i)=onLeft h (s i))
    (admit:∀i,100*(max h (s i).right+1) ≤ depth)
    (dates:(V k).k=(V m).k ∨ (V k).k=(V m).k+1)(warm:WilsonPhysicalStationBasisClock.Live R (V m).k)
    (win:aperture R (V m).k (V k).k h (M₀) (M₁) ≤ 1)
    (loc:∀i,tested (ax₀) (V m).b (V m).k (x i)∈(s i).site)(fit:∀i,FitSky (ax₀) (V m).b (V m).k (x i))
    (pos:∀i,0 ≤ roof i)(wage:∀i,‖η i‖*(θ)^Q ≤ roof i*(θ)^(rank R.family (s i).right (s i).dual)):
    Paid R V hk cb q Q w (grade) (peer) η x (∑i,roof i*WilsonPhysicalStationMixedSchurBoard.charge R (V m) s (h:=h) i depth q (x i)):=by
  apply filed R F J₀ J V hm hk ca cb eh s dr owner q Q η roof x _ loc fit pos wage
  exact WilsonPhysicalStationMixedSchurBoard.purchased R (V m) (V k) _ _ ca cb s dr bind O ρ price qty menu P house pick record admit dates warm win

end YM.Integration.WilsonPhysicalStationMixedPurchasedMarket
end
