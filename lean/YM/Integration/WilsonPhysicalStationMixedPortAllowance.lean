import YM.Integration.WilsonPhysicalStationMixedWageLimit
import YM.Integration.WilsonPhysicalStationMixedWickNamedPrice
import YM.Integration.WilsonPhysicalStationMixedHomogeneousCash
import YM.Integration.WilsonPhysicalStationMixedSchurBoard
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedPortAllowance
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
open WilsonPhysicalStationMixedHomogeneousCash (wallet)
open WilsonPhysicalStationMixedWageLimit (allowance charged)
variable {G:Gauge}(R:Run G){h:ℕ}(s:Slot R.family)(u:(standard R.family).Field h)(q:ℕ)
def fee (D m:ℕ):ℝ:=
  wallet R u*allowance R (onLeft h s) q D m+
    (12:ℝ)^q*|WilsonPhysicalStationMixedWickNamedPrice.price R (onLeft h s) u|/((D:ℝ)+1)
theorem original (simple:G.Simple){I:Type*}{l:Filter I}{D m:I→ℕ}
    (deep:Tendsto D l atTop)(late:Tendsto m l atTop):
    Tendsto (fun i=>fee R s u q (D i) (m i)) l (𝓝 0):=by
  let fixed:ℝ:=12^q*|WilsonPhysicalStationMixedWickNamedPrice.price R (onLeft h s) u|
  have first:= (WilsonPhysicalStationMixedWageLimit.original R (onLeft h s) simple q deep late).const_mul (wallet R u)
  have second:= (tendsto_one_div_add_atTop_nhds_zero_nat.comp deep).const_mul fixed
  simpa [fee,fixed,div_eq_mul_inv] using first.add second
theorem cash {D m:ℕ}(A:Vane R.family m)(ξ:Points 2)(χ:ℂ)
    (loc:tested R.family.path.levels A.b A.k ξ∈s.site)(bounded:‖χ‖≤(12:ℝ)^q):
    wallet R u*WilsonPhysicalStationMixedSchurBoard.charge R A (fun _:Unit=>s) (h:=h) () D q ξ+
     ‖χ‖*(WilsonPhysicalStationMixedWickNamedPrice.price R (onLeft h s) u/((D:ℝ)+1)) ≤ fee R s u q D A.k:=by
  have wp:0 ≤ wallet R u:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have denom:0 < (D:ℝ)+1:=by positivity
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (charged R (onLeft h s) q D A.k loc) wp
  · rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right bounded (abs_nonneg _))) denom.le
end YM.Integration.WilsonPhysicalStationMixedPortAllowance
end
