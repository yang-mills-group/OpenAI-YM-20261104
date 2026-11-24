import YM.Integration.WilsonPhysicalStationBasisClock
/-! Signed finite two-post income on the original elected column and its actual lower field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationBasisWindow
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

open WilsonPhysicalStationBasisImpact (seen)
open WilsonPhysicalStationBasisRoof (amount)
open WilsonPhysicalStationMeasuredCash (aperture)
local notation "E₀"=>aperture R A.k B.k h₀ (mag (L₀) A.b A.k) (mag (L₀) B.b B.k)
def Filed {N p:ℕ} (ca:A.checked f H D)(cb:B.checked f H D')(top:B.k < N)(w:R.family.label h₀) : Prop :=
  if B.k=A.k then WilsonPhysicalStationCoincidentLower.Receipt R A B h₀ e da db (p:=p) ca cb top X.raw w
  else WilsonPhysicalStationSelectedLower.Receipt R A B h₀ e da db (p:=p) ca cb top X.raw w

include L fac in
theorem original (hg:G.Simple)(ca:A.checked f H D)(cb:B.checked f H D')
    (dates:B.k=A.k ∨ B.k=A.k+1)(horizon:h₀=e+1)(weight:((F₀).grades X.raw).1=h₀)
    (warm:WilsonPhysicalStationBasisClock.Live R A.k)(window:E₀ ≤ 1)
    (sold:Sold R A X (by omega) step ca):
    ∀ᶠ N:ℕ in atTop,∀p:ℕ,∀top:B.k < N,∀w:R.family.label h₀,
      Filed R X da db A B (p:=p) (e:=e) ca cb top w→
      ∀ξ:Points 2,tested (L₀) A.b A.k ξ∈X.site→FitSky (L₀) A.b A.k ξ→
      seen R X da db A B (p:=p) cb top w ξ ≤ amount R X step A.k:=by
  rcases dates with same|next
  · have gate:e₁ ≤ 1/2:=by rw [same];exact warm.old
    filter_upwards [WilsonPhysicalStationBasisTransfer.coincident R fac X da db A B ca cb same horizon weight warm.old gate warm.large sold] with N ear
    intro p top w stamped ξ inside fit
    exact WilsonPhysicalStationBasisImpact.coincident R X da db A B cb same top w ξ inside window
      (warm.coincident _) (ear p top w (by simpa only [Filed,if_pos same] using stamped) ξ inside fit)
  · have neq:B.k≠A.k:=by omega
    have gate:e₁ ≤ 1/2:=by rw [next];exact warm.fine
    have inter:∀N p:ℕ,A.k < N→shrink R.family A.k N p ≤ 6*shrink R.family B.k N p:=by
      intro N p live;rw [next];exact warm.slope N p live
    filter_upwards [WilsonPhysicalStationBasisTransfer.advance R L fac X da db A B hg ca cb next horizon weight warm.old gate warm.large inter sold] with N ear
    intro p top w stamped ξ inside fit
    exact WilsonPhysicalStationBasisImpact.advance R X da db A B cb top w ξ inside window warm.thermal
      (by rw [next];exact warm.adjacent _) (ear p top w (by simpa only [Filed,if_neg neq] using stamped) ξ inside fit)
end YM.Integration.WilsonPhysicalStationBasisWindow
end
