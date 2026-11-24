import YM.Integration.WilsonMovingForkStencilHousing
import YM.Integration.WilsonAddressedPublicFirstCentres

/-! Every original child with the declared physical parent has its actual birthday address. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterCapturedSites
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

private theorem cancel {A B : Levels G} (e : A=B) (w : Digits B (Fin n)) :
    onLevels e (onLevels e.symm w) = w := by cases e; rfl

theorem atTop (ξ : Fin n → Site (R.family.side K per)) :
    physical R ξ (le_refl K) = ξ := by
  funext v
  let reg := R.family.S.toDepth (le_refl K) per
  have fixed : reg.embed (ξ v) = ξ v :=
    reg.embed_injective ((Next.Rank.Station.embed_comp reg reg reg _).symm)
  exact (congrArg reg.parent fixed).symm.trans (reg.embed_parent _)

theorem origin (ξ : Fin n → Site (R.family.side K per)) (active : first+1 ≤ K)
    (captured : ∀v, physical R ξ active v = 0) : footprint R ξ active = 0 := by
  funext v
  change lift (physical R ξ active v) = 0
  rw [captured]
  funext k
  simp [lift]

theorem addressed (ξ : Fin n → Site (R.family.side (j+1+1) per)) (age : first ≤ j)
    (active : first+1 ≤ j+1+1) (captured : ∀v, physical R ξ active v = 0) :
    let tape := onLevels draw.symm (digits R ξ)
    addresses R (j+1) per (homes tape (0 : Fin n → Cover) first (j-first))
      (onLevels draw tape) = ξ := by
  have seats := WilsonAddressedPublicFirstCentres.addressed R draw active age le_rfl ξ (origin R ξ active captured)
  dsimp only
  rw [cancel draw]
  exact seats.trans (atTop R ξ)

end YM.Integration.WilsonReceivedChronologicalRosterCapturedSites
end
