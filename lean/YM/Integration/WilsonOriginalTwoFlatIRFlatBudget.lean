import YM.Integration.WilsonReceivedDepositedOrbitalBudget
import YM.Integration.WilsonOriginalTwoFlatIRFlatLedger

/-! Discarding super-target grades of a paid connected copy on the genuine
flat costs the actual funded roll salaries and a positive coupling power. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.Integration.WilsonOriginalTwoFlatIRFlatBudget
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary QuadraticLocal.Affinity
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision Tree Exterior PhysicalNext.Repeat.Legato
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada FVA1Physical.TwoReset
open WilsonVacuumPreResetStationaryChange WilsonOriginalPrimerReplicatedInk PhysicalForestMarkedRay PhysicalForestRay
open FreeResolvent WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonOriginalPointCompactRoster WilsonOriginalThreeCopiedCharts
open scoped Classical BigOperators ContDiff Topology
open LocalComparison Comparison.RG02.Cumulants Comparison.RG02.Assembly Order AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalThreePurchasedRays (prescribed)
attribute [local instance] Gauge.frobInner
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet WilsonOriginalCensusCopySlate
open WilsonOlderFreshGraphSlate (Copy)
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
open WilsonNeutralTwoPrintPathCensus (slates)
open WilsonNeutralTwoPrintPathJet (diagonal)

open WilsonGeneralArityCopyAccount WilsonOriginalCensusDatedMaterial WilsonCoeffUV.Blue
open Primitives.TwoWave AllOrder.Haiku Stationary


variable {G:Gauge}{n:ℕ}{R:Run G}{N i q:ℕ}{k:Fin n → ℕ}{σ:ℝ}
  {side:Side}{P:Passport side (Fin n)}{I:Type}{B:I → Binder P (Stock.census (Fin n))}
  (H:Material R N i q k σ B)(z:I)


open WilsonCoeffUV.Wheel.Mark (mass)
def budget (l:I):ℝ:=
  let S:=(B l).mode.val
  (q+1:ℕ)*((mass k S+q+1:ℕ)*((∏v∈S,‖H.source l v‖)*
    (R.family.path.levels.clock.hatBeta i^H.allowance*H.amplitude^S.card)))

theorem original (l:I):∑e:Fin (q+1),(words H l).fare e≤budget H l:=by
  have paid:=WilsonReceivedDepositedOrbitalBudget.posted H l
  simp only [Marker.Poly.toll,Finset.prod_const_one,one_mul] at paid
  change Real.exp _ * (1+∑a,(words H l).fare a)≤Real.exp _*(1+budget H l) at paid
  exact (add_le_add_iff_left 1).mp (le_of_mul_le_mul_left paid (Real.exp_pos _))

end YM.Integration.WilsonOriginalTwoFlatIRFlatBudget
end
