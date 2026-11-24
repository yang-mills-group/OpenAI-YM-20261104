import YM.Integration.WilsonPhysicalStationMixedPurchasedMarket
import YM.Integration.WilsonPhysicalStationMixedFixedSensor
import YM.Integration.WilsonPhysicalStationMixedSamePort
import YM.Integration.WilsonPhysicalStationMixedWickPlacement
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedOwnedSensor
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
    (s:Slot R.family)(dr:s.right < m+1)
    {w:Head R.family h→(ℕ×ℕ)→R.family.label h}{v:Head R.family h→R.family.label h}{g:ℝ}
    (owner:WilsonPhysicalStationBasisOwners.Earned R F (ℓ:=ℓ) J₀ J V hm hk ca cb eh w v g)
    (q:ℕ)(ξ:Points 2)
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
def scale (g:ℝ)(h q:ℕ):ℂ:=((((V k).wheel.r/(V m).wheel.r)^h*g^q:ℝ):ℂ)
local notation "χ₀"=>scale R V (m:=m) (k:=k) g h q
def tariff (q:ℕ)(u:(C₀).Field h)(g:ℝ):ℝ:=
  wallet R u*WilsonPhysicalStationMixedSchurBoard.charge R (V m) (fun _:Unit=>s) (h:=h) () depth q ξ+
    ‖scale R V (m:=m) (k:=k) g h q‖*(WilsonPhysicalStationMixedWickNamedPrice.price R (onLeft h s) u/((depth:ℝ)+1))

include owner dr in
theorem original (bind:Binding R.family)(O:HaarBudget G)(ρ:ChartRatio G)(price:ℕ→ℝ)(qty:ℕ→ℕ)
    (menu:∀D,Fin (qty D)→Slot R.family)(P:Tapes.Panel depth)
    (house:WilsonMovingForkReporterMixedHouses.Held (f:=f) R bind O ρ H price qty menu P (V m))
    (pick:Fin (qty depth))(record:menu depth pick=onLeft h s)
    (admit:100*(max h s.right+1) ≤ depth)
    (dates:(V k).k=(V m).k ∨ (V k).k=(V m).k+1)(warm:WilsonPhysicalStationBasisClock.Live R (V m).k)
    (win:aperture R (V m).k (V k).k h (M₀) (M₁) ≤ 1)
    (loc:position∈s.site)(fit:FitSky (ax₀) (V m).b (V m).k ξ)
    {ak bk aa ba ar br:ℝ}
    (fine:Filed (f:=f) (l:=ℓ) J₀ J V h k ak bk)(leftA:Filed (f:=f) (l:=ℓ) J₀ J V h m aa ba)
    (rightA:Filed (f:=f) (l:=ℓ) J₀ J V s.right m ar br)(simple:G.Simple)(below:(ℓ:Filter _) ≤ f.fuse)
    (big:1 ≤ θ)(u:(C₀).Field h)(pure:Pure R q u):
    ‖ear R (S:=S) ((V m).wheel.r • position) (J.U m s.right peer₁)
      ((J.U k h u-χ₀ • J.U m h u)-earlier R (S:=S) v u)‖*θ^q₁ ≤
        θ^q*tariff R V (m:=m) (k:=k) (depth:=depth) s ξ q u g:=by
  let svc:Unit→Slot R.family:=fun _=>s
  let pts:Unit→Points 2:=fun _=>ξ
  have paid:=WilsonPhysicalStationMixedPurchasedMarket.original R F J₀ J V hm hk ca cb eh svc (fun _=>dr) owner q q₁
    (WilsonPhysicalStationMixedFixedSensor.tip ()) (fun _=>1) pts bind O ρ price qty menu P house (fun _=>pick) (fun _=>record) (fun _=>admit)
    dates warm win (fun _=>loc) (fun _=>fit) (fun _=>zero_le_one) (fun i=>by cases i; simp [WilsonPhysicalStationMixedFixedSensor.tip,svc])
  have quoted:=WilsonPhysicalStationMixedFixedSensor.original R F J₀ J V hk cb q q₁ w v
    (fun _:Unit=>r₁) (fun _=>peer₁) pts ca simple below fine (fun _=>⟨ar,br,rightA⟩) (fun a=>(owner.lower a).1)
    owner.kinetic () paid (fun _=>fit) u pure
  have original:=WilsonPhysicalStationMixedWickPlacement.occupied R bind O ρ price P (V m) ca house (onLeft h s)
    ⟨pick,record⟩ (Nat.lt_succ_of_le hm) dr admit
  have near:=WilsonPhysicalStationMixedSamePort.original R F J₀ J V (onLeft h s)
    (Nat.lt_succ_of_le hm) dr ca leftA rightA simple below original u q pure ξ loc fit big
  apply WilsonPhysicalStationMixedContrastBill.joined R _ _ _ _ _ χ₀ (WilsonPhysicalStationMixedBallotCash.pair (C₀) h s.right position u peer₁) (T:=θ) (zero_le_one.trans big) q q₁
  · simpa only [Fintype.sum_unique,one_mul,pts,svc,scale] using quoted
  · exact near

end YM.Integration.WilsonPhysicalStationMixedOwnedSensor
end
