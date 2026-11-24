import YM.Integration.WilsonOriginalCensusFaceIncome
import YM.Integration.WilsonIndependentCollarMaterialWallet
import YM.Integration.WilsonIndependentCollarMaterialCost

/-! The original physical cable fits the salary of its own rooted independent material. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFixedTestCensusGeometry
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
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology

open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedPin WilsonOlderFreshConnectedAppointment FundedMarkedCoverRows
open WilsonCoeffUV.Bank.Ticket

open WilsonOlderFreshConnectedBirth WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp
open WilsonOlderFreshConnectedBinding


open QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary Stationary
open WilsonOriginalPrimerReceipts WilsonNeutralTwoPrintPathJet
open Primitives.TwoWave AllOrder.Haiku AllOrder.Ink Response PertExtension.Series

open WilsonNeutralTwoPrintPathRoll WilsonOlderFreshConnectedAssembly
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker FVA1Physical FVA1Physical.TwoReset


open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Mosaic.Near
open WilsonNeutralTwoPrintPathRead

open WilsonNeutralTwoPrintPathFixed (parcel)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedFixedDigitCanonical (fixed)
open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonNeutralTwoPrintPathQuoted (bill)

open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Multi
open WilsonNeutralTwoPrintPathCensus (slates)
open WilsonNeutralTwoPrintPathDatedPolynomial (row sheet entry)
open WilsonReceivedCoverGrade (Same)
open FundedMarkedPathSelection (output)

open WilsonOriginalCensusDatedMaterial (Material words mounts)
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead WilsonNeutralTwoPrintPeg
open WilsonNeutralTwoPrintPathPolynomial RegulatorIR.Diagram

open WilsonOriginalCensusFaceSites (binder port pin frill root)
open WilsonOriginalCensusDatedSheets (sideValue)
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonReceivedCompactVerseEntrance (submit)
open WilsonOriginalCensusFaceSheet (Addressed)
open WilsonReceivedDepositedOrbitalPrint (front)
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express
open WilsonOriginalCensusFaceSites (root)
variable {G:Gauge}{n N i q:ℕ}{k:Fin n → ℕ}{σ:ℝ}{R:Run G}{side:Side}
  (y:Fin n → Cover)(L:Material R N i q k σ (binder side y))(t:Case L.tests)
  (held:Addressed y L t)
local notation "labels" => Hot (Stock.census (Fin n))

private theorem distance (x z:Cover):
    separation (wrap side x) (wrap side z) ≤ Bank.terrain.gap x z:=by
  rw [separation_comm]
  unfold Lattice.separation
  rw [←map_sub]
  exact Next.Free.within_size ..

include held in
theorem span (s:labels):
    let z:=toe s.val.val (L.pin s) (L.root s) (L.frill s)
    ((binder side y) s).length ≤ 32*feeH z (L.pin s) s.val.val:=by
  intro z
  have anchor:wrap side (z (L.pin s))=wrap side (root y s):=by
    have start:z (L.pin s)=L.root s:=by simp [z,toe]
    rw [start,held.center s,WilsonOriginalCensusFaceSites.center]
  refine (WilsonOriginalCensusFaceSites.tariff side y s).trans ?_
  calc
    _ ≤ ∑ v∈s.val.val,4*Bank.terrain.gap (z (L.pin s)) (z v):=by
      apply Finset.sum_le_sum
      intro v member
      rw [←anchor,←held.agrees s v member]
      exact Nat.mul_le_mul_left 4 (distance (side:=side) _ _)
    _ = 4 * ∑ v∈s.val.val,Bank.terrain.gap (z (L.pin s)) (z v):=(Finset.mul_sum ..).symm
    _ ≤ _:=by unfold feeH;omega

include held in
theorem submitted (s:labels):
    Real.exp (σ*((binder side y) s).length)*
        WilsonIndependentCollarSlateIntensity.amount (words L s) ((binder side y) s).center  ≤ 
      WilsonIndependentCollarMaterialIntensity.price L s:=by
  simpa using WilsonIndependentCollarMaterialIntensity.mounted L s 0
    (by simp only [Nat.zero_add]; exact span y L t held s)

end YM.Integration.WilsonOriginalFixedTestCensusGeometry
end
