import YM.Integration.WilsonReceivedChronologicalRosterCapturedSites
import YM.Integration.WilsonAddressedPublicFirstRoseHomes

/-! Physical parent housing for the first transfer at the actual captured position. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterHome
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

variable {G:Gauge}{R:Run G}{n first K per q:ℕ}
  {V:Realm G (q+1) Credit.leanC}(draw:V.draws=R.family.path.levels)
  (ξ:Fin n → Site (R.family.side K per))(start:first+1 ≤ K)

local notation "tapeOf" => WilsonMovingForkStencilHousing.cells

theorem housed (arrived:∀v,physical R ξ start v=0)
    (j:ℕ)(age:first ≤ j)(budget:j+1+1 ≤ K):
    let tape:=tapeOf draw ξ
    let y:=homes tape (0:Fin n → Cover) first (j-first)
    let chosen := WilsonIndependentCollarCanonicalCofinalSeats.addresses R (j+1) per y (onLevels draw tape)
    let P := Passport.point chosen
    ∀v:Fin n,sites R (P.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
      (Nat.succ_le_succ age) v∈({0}:Support (R.family.side (first+1) per)):=by
  have head := WilsonReceivedChronologicalRosterCapturedSites.origin R ξ start arrived
  obtain ⟨a,rfl⟩:=Nat.exists_eq_add_of_le age
  have upper:first+a+1+1 ≤ K:=by omega
  have lower:first+1 ≤ first+a+1:=by omega
  have nx:=WilsonReceivedChronologicalMaterialStream.next (R:=R) (draw:=draw) (tapeOf draw ξ)
    (0:Fin n → Cover) (show first ≤ first+a by omega)
  rw [show first+a+1-first=a+1 by omega] at nx
  have lay:=WilsonReceivedChronologicalMaterialSites.resident R draw ξ start a (first+1) upper lower
    (port _ (chartIn (loose R.family.path.levels (first+a+1))
      (homes (tapeOf draw ξ) 0 first (first+a-first)) ((onLevels draw (tapeOf draw ξ)) (first+a+1))))
    (by rw [head];exact congrArg (port _) nx.symm)
    Finset.univ ({0}:Support (R.family.side (first+1) per)) (by intro i _;simpa using arrived i)
  dsimp only
  have aligned : WilsonIndependentCollarCanonicalCofinalSeats.addresses R (first+a+1) per
      (homes (tapeOf draw ξ) 0 first (first+a-first)) (onLevels draw (tapeOf draw ξ)) =
      fun v => wrap (R.family.side (first+a+1+1) per) (chartIn (loose R.family.path.levels (first+a+1))
        (homes (tapeOf draw ξ) 0 first (first+a-first)) ((onLevels draw (tapeOf draw ξ)) (first+a+1)) v) :=
    funext (WilsonIndependentCollarCanonicalCofinalSeats.actual R _ per _ _)
  rw [aligned]
  exact fun i=>lay i (Finset.mem_univ i)


end YM.Integration.WilsonReceivedChronologicalRosterHome
end
