import YM.Integration.WilsonReceivedChronologicalRosterExternalSites
import YM.Integration.WilsonReceivedChronologicalRosterCapturedSites
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterCaptureSite
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Bank.Ticket
open WilsonOlderFreshConnectedRobe
open WilsonReceivedChronologicalMaterialLine (homes)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonOriginalCensusFaceSites (port)
open WilsonOriginalOccupiedCorridor (sites)
open WilsonReceivedChronologicalMaterialSites (digits footprint physical)
open WilsonCoeffUV.Winding
open OriginalIssuedMarkedRows
open WilsonMovingForkSeededPoint (seats)
open scoped BigOperators Classical


open WilsonReceivedChronologicalMaterialSites (physical digits footprint)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonIndependentCollarCanonicalCofinalSeats (addresses)
open WilsonReceivedChronologicalMaterialLine (homes)

variable {G : Gauge} (R : Run G) {n q per first j K : ℕ}
  {V : Realm G (q+1) Credit.leanC} (draw : V.draws = R.family.path.levels)

open WilsonReceivedFixedDigitHistory (Digits)

theorem original (ξ:Fin n → Site (R.family.side K per))(stage:first≤j)(jk:j+1≤K)
    (capture:∀i,physical R ξ jk i=0)(i:Fin n):
    wrap (R.family.side (j+1) per) (homes (onLevels draw.symm (digits R ξ))
      (0:Fin n → Cover) first (j-first) i)=0:=by
  have start:first+1≤K:=(Nat.succ_le_succ stage).trans jk
  have early:=WilsonReceivedChronologicalRosterExternalSites.predecessor R ξ (Nat.succ_le_succ stage) jk capture
  have flat:=WilsonReceivedChronologicalRosterCapturedSites.origin R ξ start early
  obtain ⟨a,rfl⟩:=Nat.exists_eq_add_of_le stage
  have actual:=WilsonReceivedChronologicalMaterialSites.itinerary R draw ξ start a jk i
  rw [flat] at actual
  simpa only [Nat.add_sub_cancel_left] using actual.trans (capture i)

end YM.Integration.WilsonReceivedChronologicalRosterCaptureSite
end
