import YM.Integration.WilsonPhysicalStationBasisIncome
import YM.Integration.WilsonPhysicalStationWickCeiling
import YM.Integration.WilsonPhysicalStationAdjacentRate
import YM.Integration.WilsonPhysicalStationCoincidentRate
/-! Uniform original reflected price on two increasing physical parameters. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationBasisRoof
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus MergeProof Matric Gram
open PhysicalNext.Repeat.Legato Bandage Campaign
open Next.Foundations OPE Work.G08
open Next.Rank Next.Rank.East Next.Rank.Price MergeProof.East
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress
open Trace.Physical.GermGraph
open WilsonPhysicalStationFactoryGerm (incoming)
open WilsonPhysicalStationRawReading (err eng)
open WilsonPhysicalStationFineCorrection (measured)
open WilsonPhysicalStationRegisteredDiagonal (ratio ceiling)
open WilsonPhysicalStationRegisteredFiling (rate)
open WilsonPhysicalStationThermalStart (entered)
open WilsonPhysicalStationThermalCoordinates (filed)
open WilsonPhysicalStationEndCurrency (row charge)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationWeightedAxis (purse)
open WilsonPhysicalStationThermalPair (cell)
open WilsonPhysicalStationTableJump (pair)
open Next.Rank Next.Rank.Tapes Next.Rank.Tapes.West Rise Alarm Paint Next.Rank.Station Glimmer
open Ward MergeProof.Accent Next.Rank.Ribbon
open scoped BigOperators Classical Topology

open WilsonMovingForkReporterFixedRanks (Axes)
open WilsonMovingForkReporterBasisRows (Sold)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonPhysicalStationThermalBasisOffice (rank)
open WilsonPhysicalStationBasisIncome (price)
variable {G:Gauge}(R:Run G)
def wick (X:Axes R.family):ℝ:=Classical.choose (WilsonPhysicalStationWickCeiling.original R X.weight
  (probe R.family X.dual X.turn X.arm) X.site X.compact X.separated)
theorem compact (X:Axes R.family):0≤wick R X ∧ ∀x∈X.site,
    ∑a,‖WilsonPhysicalStationObservedEntry.born R X.weight x (probe R.family X.dual X.turn X.arm) a‖≤wick R X:=
  Classical.choose_spec (WilsonPhysicalStationWickCeiling.original R X.weight
    (probe R.family X.dual X.turn X.arm) X.site X.compact X.separated)
def rent (m h:ℕ):ℝ:=|WilsonPhysicalStationAdjacentRate.tab R m h|+|WilsonPhysicalStationCoincidentRate.tariff R m|
def amount (X:Axes R.family)(D m:ℕ):ℝ:=
  let q:=rank R.family X.weight X.raw
  let Q:=rank R.family X.weight X.dual
  let n:ℝ:=Fintype.card (R.family.labels.level X.weight).Index
  2*6^q*(price R X D*4^Q*(2^q+n*rent R m X.weight)+rent R m X.weight*wick R X)

theorem project {E t r w b ρ n J c:ℝ} (q Q:ℕ)(within:E≤1)(tp:0≤t)(relative:t≤2)
    (rp:0≤r)(meter:r≤ρ)(wp:0≤w)(roof:w≤b)(size:0≤n)(jp:0≤J)(cp:0≤c)(age:c≤6^q):
    2*E*c*(J*4^Q*(t^q+n*r)+r*w)≤2*6^q*(J*4^Q*(2^q+n*ρ)+ρ*b):=by
  have hp:0≤ρ:=rp.trans meter
  have iq:=pow_le_pow_left₀ tp relative q
  have tally:t^q+n*r≤2^q+n*ρ:=add_le_add iq (mul_le_mul_of_nonneg_left meter size)
  have inner:=add_le_add (mul_le_mul_of_nonneg_left tally (mul_nonneg jp (by positivity : 0≤(4:ℝ)^Q)))
    (mul_le_mul meter roof wp hp)
  have a:2*E*c≤2*6^q:=by
    calc _≤2*1*(6:ℝ)^q:=mul_le_mul (mul_le_mul_of_nonneg_left within (by norm_num)) age cp (by norm_num)
         _=_:=by ring
  exact mul_le_mul a inner (by positivity) (by positivity)

theorem before (hg:G.Simple)(X:Axes R.family){I:Type*}{l:Filter I}{D m:I→ℕ}
    (deep:Tendsto D l atTop)(late:Tendsto m l atTop):
    Tendsto (fun i=>amount R X (D i) (m i)) l (𝓝 0):=by
  have ab:=((WilsonPhysicalStationAdjacentRate.tends R hg X.weight).comp late).abs
  have ac:=((WilsonPhysicalStationCoincidentRate.tends R hg).comp late).abs
  have tail:Tendsto (fun i=>rent R (m i) X.weight) l (𝓝 0):=by simpa [rent] using ab.add ac
  have per:Tendsto (fun i=>price R X (D i)) l (𝓝 0):=by
    simpa [WilsonPhysicalStationBasisIncome.price,div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp deep).const_mul (WilsonPhysicalStationBasisIncome.budget R X)
  let q:=rank R.family X.weight X.raw
  let Q:=rank R.family X.weight X.dual
  let n:ℝ:=Fintype.card (R.family.labels.level X.weight).Index
  have base:Tendsto (fun _:I=>(2:ℝ)^q) l (𝓝 ((2:ℝ)^q)):=tendsto_const_nhds
  simpa [amount,q,Q,n] using ((((per.mul_const ((4:ℝ)^Q)).mul
    (base.add (tail.const_mul n))).add (tail.mul_const (wick R X))).const_mul (2*(6:ℝ)^q))

end YM.Integration.WilsonPhysicalStationBasisRoof
end
