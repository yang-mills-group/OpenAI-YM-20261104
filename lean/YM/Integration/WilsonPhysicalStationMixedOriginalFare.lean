import YM.Integration.WilsonPhysicalStationMixedCourtFare
import YM.Integration.WilsonPhysicalStationMixedWickLowerLaw
import YM.Integration.WilsonPhysicalStationMixedWickChamberPorts
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedOriginalFare
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
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramFreePanel (named)
open WilsonPhysicalStationMixedWickChamberPorts (contact)
open WilsonPhysicalStationMixedWickCollege (chosen)
open WilsonPhysicalStationMixedWickLowerLaw (ceiling)
set_option quotPrecheck false
variable {G:Gauge}(R:Run G){S:Table R.family.book}(book:Deck G)(lo hi:ℕ→ℕ)(ax:ℕ→Axis)(i:ℕ)
local notation "room₀"=>chosen R (S:=S) book (lo i) (ax i)
local notation "field₀"=>(standard R.family).Field (hi i)
def refund (u:field₀)(q:ℕ)(b:(R.family.labels.level (hi i)).Index)(turn:Signed)(side:Fin 2)(D k:ℕ):ℝ:=
  let top:=contact R (S:=S) book lo hi ax i true true b turn side
  let raw:=contact R (S:=S) book lo hi ax i false true b turn side
  WilsonPhysicalStationMixedCourtFare.total R top book (lo i) (room₀).site (room₀).compact (room₀).clear
    u q (fun _=>ceiling R raw book (ax i) (room₀)) D k
theorem original (u:field₀)(q:ℕ)(simple:G.Simple){A:Type*}{l:Filter A}{D k:A→ℕ}
    (deep:Tendsto D l atTop)(late:Tendsto k l atTop){ε:ℝ}(positive:0<ε):
    ∀ᶠz in l,∀b turn side,refund R (S:=S) book lo hi ax i u q b turn side (D z) (k z)<ε:=by
  apply Filter.eventually_all.mpr
  intro b
  apply Filter.eventually_all.mpr
  intro turn
  apply Filter.eventually_all.mpr
  intro side
  exact WilsonPhysicalStationMixedCourtFare.before R (contact R (S:=S) book lo hi ax i true true b turn side)
    book (lo i) (room₀).site (room₀).compact (room₀).clear u q simple deep late
    (fun _=>ceiling R (contact R (S:=S) book lo hi ax i false true b turn side) book (ax i) (room₀)) positive
end YM.Integration.WilsonPhysicalStationMixedOriginalFare
end
