import YM.Integration.WilsonPhysicalStationBasisTransfer
import YM.Integration.WilsonPhysicalStationBasisRoof

/-! The actual original cross-table signed scalar on a compact separated roster. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationBasisImpact
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
variable {G:Gauge}(R:Run G){T:Campaign R}(L:Pillars R T){f:Extraction.Order}{S:Table R.family.book}
  (fac:Facilities R.family f S){H:(Bel R.family.book).Hierarchy}{D D' step:ℕ}
  (X:Axes R.family){e:ℕ}(da:X.weight<D+1)(db:X.weight<D'+1)
local notation "h₀"=>X.weight
local notation "F₀"=>R.family.labels.level X.weight
local notation "L₀"=>R.family.path.levels
local notation "z₀"=>probe R.family X.dual X.turn X.arm
local notation "Q₀"=>rank R.family X.weight X.dual
local notation "J₀"=>price R X step
variable (A:Vane R.family D)(B:Vane R.family D')
local notation "T₀"=>(L₀).clock.monitor A.k
local notation "e₀"=> ((L₀).params A.k).columns*err R A.k
local notation "e₁"=> ((L₀).params B.k).columns*err R B.k

open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationMeasuredCash (aperture)
open WilsonPhysicalStationObservedEntry (born)
open WilsonPhysicalStationBasisRoof (wick amount)
local notation "E₀"=>aperture R A.k B.k h₀ (Station.mag (L₀) A.b A.k) (Station.mag (L₀) B.b B.k)
local notation "q₀"=>rank R.family X.weight X.raw
local notation "n₀"=>(Fintype.card (F₀).Index:ℝ)
local notation "M₀"=>Station.mag (L₀) A.b A.k
local notation "M₁"=>Station.mag (L₀) B.b B.k
def seen {N p:ℕ}(cb:B.checked f H D')(top:B.k<N)(w:R.family.label h₀)(ξ:Points 2):ℝ:=
  let y:=entered R B (⟨h₀,db⟩:Fin (D'+1)) (p:=p) cb top (Pi.single X.raw 1)
  let χ:ℂ:=signal R N p A.k B.k h₀ q₀ (M₀) (M₁)
  let Γ:=born R h₀ (tested (L₀) A.b A.k ξ) z₀
  ‖WilsonPhysicalStationTableJump.pair R (⟨h₀,da⟩:Fin (D+1)) N p A.k (choose (L₀) A.b A.k ξ)
      (y-(R.family.factory h₀ N p).terminal w) (A.wheel.atCut (N,p) (⟨h₀,da⟩:Fin (D+1)) z₀)-χ*Γ X.raw‖
lemma self {N p m k h q:ℕ}(date:k=m)(live:m≤N)(a b:ℝ):
    signal R N p m k h q a b=aperture R m k h a b:=by
  subst k
  have ht:=shrink_pos R.family R.makes live p
  have hp:(Real.sqrt (R.family.path.β N p m))⁻¹≠0:=by
    intro bad
    exact (ne_of_gt ht) (by simp [shrink,bad])
  simp only [WilsonPhysicalStationRestoredEntry.signal,WilsonPhysicalStationMeasuredCash.aperture,div_self hp,one_pow,mul_one]
theorem advance {N p:ℕ}(cb:B.checked f H D')(top:B.k<N)(w:R.family.label h₀)(ξ:Points 2)
    (inside:tested (L₀) A.b A.k ξ∈X.site)(geometry:E₀≤1)(kinetic:ratio R A.k≤2)
    (meter:rate R A.k B.k h₀≤WilsonPhysicalStationBasisRoof.rent R A.k h₀)
    (ear:WilsonPhysicalStationClearedEar.cleared R h₀ da db A B (p:=p) cb top X.raw w ξ z₀ Q₀ J₀ 0):
    seen R X da db A B (p:=p) cb top w ξ≤amount R X step A.k:=by
  let Γ:=born R h₀ (tested (L₀) A.b A.k ξ) z₀
  let ρ:=rate R A.k B.k h₀
  have kt:0≤ratio R A.k:=div_nonneg ((L₀).budget _).threshold_pos.le ((L₀).budget _).threshold_pos.le
  have sale:=WilsonPhysicalStationBasisRoof.project (n:=n₀) q₀ Q₀ geometry kt kinetic
    (WilsonPhysicalStationWeightedAxis.positive R A.k B.k h₀) meter
    (Finset.sum_nonneg (fun i _=>norm_nonneg (Γ i))) ((WilsonPhysicalStationBasisRoof.compact R X).2 _ inside)
    (by exact_mod_cast (Nat.zero_le (Fintype.card (F₀).Index)))
    (WilsonPhysicalStationBasisIncome.nonnegative R X step) (by positivity :0≤(6:ℝ)^q₀) (le_refl _)
  apply le_trans (b:=2*E₀*6^q₀*(J₀*4^Q₀*((ratio R A.k)^q₀+n₀*ρ)+ρ*∑i,‖Γ i‖)) _ sale
  simpa only [WilsonPhysicalStationClearedEar.cleared,rank,Γ,ρ,neg_zero,Real.rpow_zero,mul_one,seen] using ear
theorem coincident {N p:ℕ}(cb:B.checked f H D')(dates:B.k=A.k)(top:B.k<N)(w:R.family.label h₀)(ξ:Points 2)
    (inside:tested (L₀) A.b A.k ξ∈X.site)(geometry:E₀≤1)
    (meter:WilsonPhysicalStationCoincidentEntry.rent R A.k≤WilsonPhysicalStationBasisRoof.rent R A.k h₀)
    (ear:WilsonPhysicalStationCoincidentDirect.cleared R h₀ da db A B (p:=p) cb top X.raw w ξ z₀ Q₀ J₀ 0):
    seen R X da db A B (p:=p) cb top w ξ≤amount R X step A.k:=by
  let Γ:=born R h₀ (tested (L₀) A.b A.k ξ) z₀
  let ρ:=WilsonPhysicalStationCoincidentEntry.rent R A.k
  have sale:=WilsonPhysicalStationBasisRoof.project (n:=n₀) q₀ Q₀ geometry (by norm_num :0≤(1:ℝ)) (by norm_num)
    (WilsonPhysicalStationCoincidentEntry.earned R A.k) meter (Finset.sum_nonneg (fun i _=>norm_nonneg (Γ i)))
    ((WilsonPhysicalStationBasisRoof.compact R X).2 _ inside) (by exact_mod_cast (Nat.zero_le (Fintype.card (F₀).Index)))
    (WilsonPhysicalStationBasisIncome.nonnegative R X step) (by norm_num :0≤(1:ℝ))
    (one_le_pow₀ (by norm_num : (1:ℝ)≤6))
  simp only [one_pow,mul_one] at sale
  apply le_trans (b:=2*E₀*(J₀*4^Q₀*(1+n₀*ρ)+ρ*∑i,‖Γ i‖)) _ sale
  simpa only [seen,self R (N:=N) (p:=p) dates (by omega) (M₀) (M₁),
    WilsonPhysicalStationCoincidentDirect.cleared,neg_zero,Real.rpow_zero,mul_one] using ear
end YM.Integration.WilsonPhysicalStationBasisImpact
end
