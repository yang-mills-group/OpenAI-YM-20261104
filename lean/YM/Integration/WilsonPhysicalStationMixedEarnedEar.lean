import YM.Integration.WilsonPhysicalStationMixedOwnedSensor
import YM.Integration.WilsonPhysicalStationMixedPortAllowance
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedEarnedEar
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
open WilsonPhysicalStationMixedOwnedSensor (scale)
local notation "χ₀"=>scale R V (m:=m) (k:=k) g h q
theorem bounded (q h:ℕ)(g:ℝ)(beam:1/8 ≤ g ∧ g ≤ 12)
    (wide:0 < (V m).wheel.r)(small:0 ≤ (V k).wheel.r)(order:(V k).wheel.r ≤ (V m).wheel.r):
    ‖scale R V (m:=m) (k:=k) g h q‖ ≤ (12:ℝ)^q:=by
  have gn:0 ≤ g:=by linarith [beam.1]
  have radius:((V k).wheel.r/(V m).wheel.r)^h ≤ 1:=pow_le_one₀ (div_nonneg small wide.le) ((div_le_one wide).2 order)
  rw [scale,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg (div_nonneg small wide.le) _) (pow_nonneg gn _))]
  exact (mul_le_mul_of_nonneg_right radius (pow_nonneg gn q)).trans (by simpa using pow_le_pow_left₀ gn beam.2 q)

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
    (wide:0 < (V m).wheel.r)(small:0 ≤ (V k).wheel.r)(order:(V k).wheel.r ≤ (V m).wheel.r)
    (big:1 ≤ θ)(u:(C₀).Field h)(pure:Pure R q u):
    ‖ear R (S:=S) ((V m).wheel.r • position) (J.U m s.right peer₁)
      ((J.U k h u-χ₀ • J.U m h u)-earlier R (S:=S) v u)‖*θ^q₁ ≤
        θ^q*WilsonPhysicalStationMixedPortAllowance.fee R s u q depth (V m).k:=by
  have earned:=WilsonPhysicalStationMixedOwnedSensor.original R F J₀ J V hm hk ca cb eh s dr owner q ξ bind O ρ price qty menu P house pick record admit dates warm win loc fit fine leftA rightA simple below big u pure
  exact earned.trans (mul_le_mul_of_nonneg_left (WilsonPhysicalStationMixedPortAllowance.cash R s u q (V m) ξ χ₀ loc
    (bounded R V (m:=m) (k:=k) q h g owner.bracket wide small order)) (pow_nonneg (zero_le_one.trans big) _))

end YM.Integration.WilsonPhysicalStationMixedEarnedEar
end
