import YM.Integration.WilsonPhysicalStationBasisPortfolio
import YM.Integration.WilsonMovingForkReporterBasisVisits
/-! Cofinal signed incomes from the true fixed-menu voters on the commissioned Scribe. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationBasisSettlement
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
open Next.Rank.Configuration Next.Rank.Atlas
open WilsonPhysicalStationFullVote (Head principal)
open WilsonPhysicalStationBasisRoof (amount)
open WilsonPhysicalStationObservedEntry (born)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationMeasuredCash (aperture)
variable {G:Gauge} (R:Run G)
theorem positive (X:Axes R.family)(d m:ℕ):0 ≤ amount R X d m:=by
  have pay:=WilsonPhysicalStationBasisIncome.nonnegative R X d
  have fee:= (WilsonPhysicalStationBasisRoof.compact R X).1
  have house (h:ℕ):0 ≤ WilsonPhysicalStationBasisRoof.rent R m h:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  have balance:=house X.weight
  dsimp only [amount]
  positivity
theorem before (hg:G.Simple){U I:Type*}[Fintype I]{l:Filter U}(X:I→Axes R.family)
    {d m:U→ℕ}(deep:Tendsto d l atTop)(late:Tendsto m l atTop)(M:I→ℝ){ε:ℝ}(small:0 < ε):
    ∀ᶠu in l,∀μ:I→ℂ,(∀i,‖μ i‖ ≤ M i)→∑i,‖μ i‖*amount R (X i) (d u) (m u) ≤ ε:=by
  have each (i:I):Tendsto (fun u=>M i*amount R (X i) (d u) (m u)) l (𝓝 0):=by
    simpa only [mul_zero] using (WilsonPhysicalStationBasisRoof.before R hg (X i) deep late).const_mul (M i)
  have total:Tendsto (fun u=>∑i,M i*amount R (X i) (d u) (m u)) l (𝓝 0):=by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _=>each i)
  filter_upwards [total.eventually_lt_const small] with u sale
  intro μ paid
  exact (Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (paid i) (positive R (X i) _ _))).trans sale.le

open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
  PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage Next.Rank Next.Rank.Tapes.West Perch Atlas Station
open Cells Edition Glyph Rise Alarm Paint Vac.Numbers Next.Rank.East Further.CorrectedLift Glimmer
open Analysis Next.UVStress Climb Ward MergeProof MergeProof.East MergeProof.Accent
theorem seated (bind:Binding R.family)(O:HaarBudget G)(J:ChartRatio G){f:Extraction.Order}
    (H:(Cells.standard R.family).Hierarchy)(price:ℕ→ℝ)(count:ℕ→ℕ)(tests:∀d,Fin (count d)→Axes R.family)
    {d h:ℕ}(pan:Tapes.Panel d)(V:Vane R.family h)
    (seen:WilsonMovingForkReporterBasisVisits.Seen (f:=f) R bind O J H price count tests pan V)
    (ca:V.checked f H h)(X:Axes R.family)(floor:100*(X.weight+1) ≤ d)(eligible:X.weight ≤ h)
    (tag:∃ t:Fin (count d),tests d t=X):Sold R V X eligible d ca:=by
  obtain ⟨_,_,purchased⟩:=seen
  obtain ⟨t,rfl⟩:=tag
  exact purchased t floor eligible

theorem homogeneous {I:Type*}[Fintype I]{N p m k h q:ℕ}(b₀ b₁:ℝ)
    (a:I→(R.family.labels.level h).Index)(level:∀i,rank R.family h (a i)=q)(Γ:(R.family.labels.level h).Index→ℂ)(μ:I→ℂ):
    (∑i,μ i*((signal R N p m k h (rank R.family h (a i)) b₀ b₁:ℂ)*Γ (a i)))=
      (signal R N p m k h q b₀ b₁:ℂ)*∑i,μ i*Γ (a i):=by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i _;rw [level];ring
end YM.Integration.WilsonPhysicalStationBasisSettlement
end
