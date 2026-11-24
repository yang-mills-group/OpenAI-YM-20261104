import YM.Integration.WilsonReceivedChronologicalRosterCapturedArchive
import YM.Integration.WilsonReceivedChronologicalRosterCapturedSites
import YM.Integration.WilsonPhysicalMovingForkVertexBoard

/-! The predecessor of each captured fork vertex keeps all its original K-child locations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterExternalSites
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


open WilsonReceivedChronologicalRosterCapturedArchive
open WilsonReceivedChronologicalMaterialCapture (placed)
open WilsonMovingForkPrintedFile (parent)
open Analysis Table Spec Extraction Next.UVStress StressFlux.Matching Cells WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking

variable {G:Gauge}(R:Run G){n f K c v per:ℕ}

private theorem zeroParent {a b:Side} (board:Ratio a b):board.parent 0 = 0 := by
  have head:lift (0:Site board.count)=0:=by funext k;simp [Lattice.lift]
  have empty:board.assemble (0,0)=0:=by
    change board.root 0+Lattice.wrap _ (lift (0:Site board.count))=0
    rw [map_zero,head,map_zero,add_zero]
  rw [←empty,board.assemble_parent]

theorem predecessor (ξ:Fin n→Site (R.family.side K per))(vc:v≤c)(ck:c≤K)
    (captured:∀i,parent R ck per ξ i=0):∀i,parent R (vc.trans ck) per ξ i=0:=by
  intro i
  let outer:=R.family.S.toDepth vc per
  let inner:=R.family.S.toDepth ck per
  change (R.family.S.toDepth (vc.trans ck) per).parent (ξ i)=0
  calc
    _ = outer.parent (inner.parent (ξ i)) :=
      Next.Rank.Station.parent_nested _ _ _ (R.family.S.toDepth_odd vc per) (R.family.S.toDepth_odd ck per) _
    _ = 0 := (congrArg outer.parent (captured i)).trans (zeroParent outer)

theorem enrolled {first:ℕ}(fv:first+1≤c)(cf:c≤f)(fine:f≤K)(y : Sites R (f,per) n)
    (captured:∀i,parent R (cf.trans fine) per (placed R fine y) i=0):
    ∃ z:Occupied (n:=n) R fine (fv.trans (cf.trans fine)) per, z.val=y :=by
  exact ⟨⟨y,predecessor R _ fv _ captured⟩,rfl⟩

theorem plotted {first:ℕ}(fv:first+1≤c)(cf:c≤f)(fine:f≤K)(o:Fin n → Cover)
    (captured:∀i,parent R (cf.trans fine) per (seats (R:=R) fine per o) i=0):
    ∃z:Occupied (n:=n) R fine (fv.trans (cf.trans fine)) per,
      z.val=fun i=>wrap (R.family.side f per) (o i) := by
  exact ⟨⟨_,predecessor R _ fv _ captured⟩,rfl⟩

end YM.Integration.WilsonReceivedChronologicalRosterExternalSites
end
