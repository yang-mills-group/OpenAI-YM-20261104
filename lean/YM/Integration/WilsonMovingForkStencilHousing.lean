import YM.Integration.WilsonReceivedChronologicalMaterialSites
import YM.Integration.WilsonPhysicalMovingForkCapturedSites

/-! Housing of every actual planted child on the fixed chronological course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingForkStencilHousing
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

abbrev cells:=onLevels draw.symm (digits R ξ)

theorem original (arrived:∀v,physical R ξ start v=0)
    (j:ℕ)(active:j∈Finset.Ico (first+1) (K-2)):
    let tape:=cells draw ξ
    let y:=homes tape (0:Fin n → Cover) first (j-first)
    let z:=chartIn (loose R.family.path.levels (j+1)) y ((onLevels draw tape) (j+1))
    let P:=port (R.family.side (j+1+1) per) z
    ∀v:Fin n,sites R (P.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
      (by have h:=(Finset.mem_Ico.mp active).1;omega:first+1 ≤ j+1) v∈({0}:Support (R.family.side (first+1) per)):=by
  have head:footprint R ξ start=0:=by
    funext i
    change lift (physical R ξ start i)=0
    rw [arrived]
    funext k
    simp [lift]
  have live:=Finset.mem_Ico.mp active
  obtain ⟨a,rfl⟩:=Nat.exists_eq_add_of_le (show first ≤ j by omega)
  have upper:first+a+1+1 ≤ K:=by omega
  have lower:first+1 ≤ first+a+1:=by omega
  have nx:=WilsonReceivedChronologicalMaterialStream.next (R:=R) (draw:=draw) (cells draw ξ)
    (0:Fin n → Cover) (show first ≤ first+a by omega)
  rw [show first+a+1-first=a+1 by omega] at nx
  have lay:=WilsonReceivedChronologicalMaterialSites.resident R draw ξ start a (first+1) upper lower
    (port _ (chartIn (loose R.family.path.levels (first+a+1))
      (homes (cells draw ξ) 0 first (first+a-first)) ((onLevels draw (cells draw ξ)) (first+a+1))))
    (by rw [head];exact congrArg (port _) nx.symm)
    Finset.univ ({0}:Support (R.family.side (first+1) per)) (by intro i _;simpa using arrived i)
  exact fun i=>lay i (Finset.mem_univ i)

theorem placed {f:ℕ}(low:first+1 ≤ f)(high:f ≤ K)(o:Fin n → Cover)
    (capture:∀i,8*‖R.family.S.gridPoint f (o i)‖ ≤ R.family.S.a (first+1+1)):
    ∀i,physical R (seats (R:=R) high per o) (low.trans high) i=0:=
  WilsonPhysicalMovingForkCapturedSites.original R low high per o capture

end YM.Integration.WilsonMovingForkStencilHousing
end
