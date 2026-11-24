import YM.Integration.WilsonPhysicalStationBasisIncome
import YM.Integration.WilsonPhysicalStationClearedEar
import YM.Integration.WilsonPhysicalStationCoincidentDirect
import YM.Integration.WilsonPhysicalStationWickCeiling

/-! Spend the selected original reporter's complete basis price after the physical lower subtraction. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationBasisTransfer
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

include L fac in
theorem advance (hg:G.Simple)(ca:A.checked f H D)(cb:B.checked f H D')(dates:B.k=A.k+1)
    (horizon:h₀=e+1)(weight:((F₀).grades X.raw).1=h₀)(gate:e₀≤1/2)(next:e₁≤1/2)(large:4≤T₀)
    (inter:∀N p:ℕ,A.k<N→shrink R.family A.k N p≤6*shrink R.family B.k N p)
    (sold:Sold R A X (by omega) step ca):
    ∀ᶠ N:ℕ in atTop,∀p:ℕ,∀top:B.k<N,∀w:R.family.label h₀,
      WilsonPhysicalStationSelectedLower.Receipt R A B h₀ e da db (p:=p) ca cb top X.raw w→
      ∀ξ:Points 2,tested (L₀) A.b A.k ξ∈X.site→FitSky (L₀) A.b A.k ξ→
      WilsonPhysicalStationClearedEar.cleared R h₀ da db A B (p:=p) cb top X.raw w ξ z₀ Q₀ J₀ 0:=by
  have hp:=WilsonPhysicalStationBasisIncome.nonnegative R X step
  filter_upwards [WilsonPhysicalStationBasisIncome.original R A X (by omega) ca (by linarith) sold] with N paid
  intro p top w stamp ξ inside fit
  obtain ⟨low,high,foreign⟩:=paid p (by omega) ξ inside fit
  have ear:=WilsonPhysicalStationMeasuredEar.original R L fac A B h₀ e da db (p:=p) hg ca cb dates top
    horizon gate X.raw weight w stamp ξ z₀ Q₀ J₀ 0 hp large (by norm_num) low high foreign
  exact WilsonPhysicalStationMeasuredCash.original R A B h₀ da db (p:=p) cb dates top X.raw w ξ z₀ Q₀
    X.ordered J₀ 0 hp large next (inter N p (by omega)) ear

include fac in
theorem coincident (ca:A.checked f H D)(cb:B.checked f H D')(dates:B.k=A.k)
    (horizon:h₀=e+1)(weight:((F₀).grades X.raw).1=h₀)(gate:e₀≤1/2)(next:e₁≤1/2)(large:4≤T₀)
    (sold:Sold R A X (by omega) step ca):
    ∀ᶠ N:ℕ in atTop,∀p:ℕ,∀top:B.k<N,∀w:R.family.label h₀,
      WilsonPhysicalStationCoincidentLower.Receipt R A B h₀ e da db (p:=p) ca cb top X.raw w→
      ∀ξ:Points 2,tested (L₀) A.b A.k ξ∈X.site→FitSky (L₀) A.b A.k ξ→
      WilsonPhysicalStationCoincidentDirect.cleared R h₀ da db A B (p:=p) cb top X.raw w ξ z₀ Q₀ J₀ 0:=by
  have hp:=WilsonPhysicalStationBasisIncome.nonnegative R X step
  filter_upwards [WilsonPhysicalStationBasisIncome.original R A X (by omega) ca (by linarith) sold] with N paid
  intro p top w stamp ξ inside fit
  obtain ⟨low,high,foreign⟩:=paid p (by omega) ξ inside fit
  have ear:=WilsonPhysicalStationCoincidentGrant.mounted R fac A B h₀ e da db (p:=p) ca cb dates top
    horizon gate X.raw weight w stamp ξ z₀ Q₀ J₀ 0 hp large (by norm_num) low high foreign
  exact WilsonPhysicalStationCoincidentCash.original R A B h₀ da db (p:=p) cb dates top X.raw w ξ z₀ Q₀
    X.ordered J₀ 0 hp large next ear
end YM.Integration.WilsonPhysicalStationBasisTransfer
end
