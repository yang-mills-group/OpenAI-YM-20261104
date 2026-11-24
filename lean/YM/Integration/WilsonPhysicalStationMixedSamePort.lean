import YM.Integration.WilsonPhysicalStationMixedContrastBill
import YM.Integration.WilsonPhysicalStationMixedPortVoter
import YM.Integration.WilsonPhysicalStationMixedWickNamedPrice
import YM.Integration.WilsonPhysicalStationMixedWickRespondents
import YM.Integration.WilsonPhysicalStationMixedBallotCash
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedSamePort
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
open WilsonPhysicalStationMixedBasisSale (Sold)
open WilsonPhysicalStationMixedWickTest (reference)
open WilsonPhysicalStationMixedPortVoter (Pure)
open WilsonPhysicalStationMixedBallotCash (pair)
open WilsonPhysicalStationLowerReceiver (ear)
open WilsonPhysicalStationThermalRanks (probe)
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}(J₀:ℝ→tower S)(J:Scaling S)
    (V:∀i,Vane R.family i){m depth:ℕ}(s:Slot R.family)(dl:s.left < m+1)(dr:s.right < m+1)(ca:(V m).checked f H m)
set_option quotPrecheck false
local notation "T₀"=>R.family.path.levels.clock.monitor (V m).k
local notation "y₀"=>tested R.family.path.levels (V m).b (V m).k
local notation "C₀"=>standard R.family
local notation "z₀"=>probe R.family s.dual s.turn s.arm
local notation "q₁"=>rank R.family s.right s.dual

theorem born {h r:ℕ}(u:(C₀).Field h)(z:(C₀).Field r)(x:Points 2):
    reference R.family (ladder R.family h u) z x=WilsonPhysicalStationMixedBallotCash.pair (C₀) h r x u z:=by
  unfold WilsonPhysicalStationMixedWickTest.reference WilsonPhysicalStationMixedWickTest.fields
  rw [Further.CorrectedLift.ladder_reads]
  rfl

include F in
theorem original {ak bk ar br:ℝ}(left:Filed (f:=f) (l:=ℓ) J₀ J V s.left m ak bk)
    (right:Filed (f:=f) (l:=ℓ) J₀ J V s.right m ar br)(simple:G.Simple)(below:(ℓ:Filter _) ≤ f.fuse)
    (bought:Sold R (V m) s dl dr depth ca)(u:(C₀).Field s.left)(q:ℕ)(pure:Pure R q u)
    (ξ:Points 2)(member:y₀ ξ∈s.site)(fits:FitSky R.family.path.levels (V m).b (V m).k ξ)(big:1 ≤ (T₀)):
    ‖ear R (S:=S) ((V m).wheel.r • y₀ ξ) (J.U m s.right (z₀)) (J.U m s.left u)-
      WilsonPhysicalStationMixedBallotCash.pair (C₀) s.left s.right (y₀ ξ) u (z₀)‖*(T₀)^(q₁) ≤
        WilsonPhysicalStationMixedWickNamedPrice.price R s u/((depth:ℝ)+1)*(T₀)^q:=by
  rw [←born,WilsonPhysicalStationLowerReceiver.evaluated]
  apply WilsonPhysicalStationMixedContrastBill.stationed big q (q₁) depth
  exact WilsonPhysicalStationMixedWickNamedPrice.original R F J₀ J V s dl dr ca left right simple below bought
    u q (fun a live=>congrArg Prod.snd (pure a live)) ξ member fits

end YM.Integration.WilsonPhysicalStationMixedSamePort
end
