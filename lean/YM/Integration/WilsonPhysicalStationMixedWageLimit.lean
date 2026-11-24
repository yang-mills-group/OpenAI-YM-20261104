import YM.Integration.WilsonPhysicalStationMixedMeasuredTicket
import YM.Integration.WilsonPhysicalStationMixedCeiling
/-! Uniform smallness on the originally enrolled compact mixed grades, prior to both regulators. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWageLimit
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open Next.Rank.Ribbon Table Trace.Pilot Trace PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical

open WilsonMovingForkReporterRankCourse (surplus)
open WilsonMovingForkReporterMixedBasis (Slot Posted ordered ranked flat measured)
open WilsonMovingForkReporterRankMarket (amount)
open WilsonPhysicalStationMixedWickPair (cell)
open WilsonPhysicalStationMixedWickTest (votes reference)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonPhysicalStationThermalBasisOffice (rank)
open WilsonOriginalBlissMixedGram (grades)
open scoped Classical BigOperators Topology
open WilsonPhysicalStationMixedBasisSale (fee Sold)
open WilsonPhysicalStationMixedBilledPort (base)
open WilsonPhysicalStationMixedListener (value)
open WilsonPhysicalStationMeasuredCash (aperture)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationMixedChartCharge (wage)
open WilsonPhysicalStationThermalStart (entered)
open WilsonPhysicalStationMixedMeasuredTicket (capital rate)
open WilsonPhysicalStationBasisRoof (rent)
variable {G:Gauge}(R:Run G)(v:Slot R.family)
local notation "Q₀"=>rank R.family v.right v.dual
local notation "z₀"=>probe R.family v.dual v.turn v.arm

def ceiling:ℝ:=Classical.choose (WilsonPhysicalStationMixedCeiling.original R v.left (z₀) v.site v.compact v.clear)
theorem compact:0≤ceiling R v ∧ ∀x∈v.site,∑a,‖base R v.left (z₀) x a‖≤ceiling R v:=
  Classical.choose_spec (WilsonPhysicalStationMixedCeiling.original R v.left (z₀) v.site v.compact v.clear)

def allowance (q D m:ℕ):ℝ:=wage R q (Q₀) (rate R v D) (ceiling R v) m v.left

theorem charged (q D m:ℕ){x:Points 2}(inside:x∈v.site):
    wage R q (Q₀) (rate R v D) (∑a,‖base R v.left (z₀) x a‖) m v.left≤allowance R v q D m:=by
  have rp:0≤rent R m v.left:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  unfold allowance wage
  exact mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left ((compact R v).2 x inside) rp) _) (by positivity)

theorem original (simple:G.Simple)(q:ℕ){I:Type*}{l:Filter I}{D m:I→ℕ}
    (deep:Tendsto D l atTop)(late:Tendsto m l atTop):
    Tendsto (fun i=>allowance R v q (D i) (m i)) l (𝓝 0):=by
  have ab:=((WilsonPhysicalStationAdjacentRate.tends R simple v.left).comp late).abs
  have ac:=((WilsonPhysicalStationCoincidentRate.tends R simple).comp late).abs
  have tail:Tendsto (fun i=>rent R (m i) v.left) l (𝓝 0):=by simpa [rent] using ab.add ac
  have per:Tendsto (fun i=>rate R v (D i)) l (𝓝 0):=by
    simpa [WilsonPhysicalStationMixedMeasuredTicket.rate,div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp deep).const_mul (capital R v)
  let n:ℝ:=Fintype.card (R.family.labels.level v.left).Index
  have steady:Tendsto (fun _:I=>(2:ℝ)^q) l (𝓝 ((2:ℝ)^q)):=tendsto_const_nhds
  simpa [allowance,wage,n] using ((((per.mul_const ((4:ℝ)^(Q₀))).mul
    (steady.add (tail.const_mul n))).add (tail.mul_const (ceiling R v))).const_mul (2*2^(Q₀)*(12:ℝ)^q))

theorem before (simple:G.Simple)(q:ℕ){I:Type*}{l:Filter I}{D m:I→ℕ}
    (deep:Tendsto D l atTop)(late:Tendsto m l atTop){ε:ℝ}(positive:0<ε):
    ∀ᶠ i in l,∀x∈v.site,wage R q (Q₀) (rate R v (D i)) (∑a,‖base R v.left (z₀) x a‖) (m i) v.left < ε:=by
  filter_upwards [(original R v simple q deep late).eventually_lt_const positive] with i small x inside
  exact (charged R v q (D i) (m i) inside).trans_lt small
end YM.Integration.WilsonPhysicalStationMixedWageLimit
end
