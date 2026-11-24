import YM.Integration.WilsonOriginalCensusDatedMaterial

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalBudget
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
variable {G:Gauge}{n:ℕ}{R:Run G}{N i q:ℕ}{k:Fin n → ℕ}{σ:ℝ}
  {side:Side}{P:Passport side (Fin n)}{I:Type}{B:I → Binder P (Stock.census (Fin n))}

open WilsonOriginalCensusDatedMaterial (Material words)
variable {R:Run G}{N j q:ℕ}{k:Fin n → ℕ}{σ:ℝ}{B:I → Binder P (Stock.census (Fin n))}
  (H:Material R N j q k σ B)

def amount (l:I):ℝ:=
  let T:=(B l).mode.val
  Real.exp (σ*(B l).length)*(1+(q+1:ℕ)*((mass k T+q+1:ℕ)*
    ((∏v∈T,‖H.source l v‖)*(R.family.path.levels.clock.hatBeta j^H.allowance*H.amplitude^T.card))))

theorem posted (l:I):
    Real.exp (σ*(B l).length)*(1+∑a,(words H l).fare a) ≤
      Poly.toll (fun _:Fin n=>(1:ℝ)) (B l).mode*amount H l:=by
  have fare:=WilsonOlderFreshConnectedBirth.account R H.realm H.start H.paid N (H.pin l) H.prior
    (H.included l) (H.marked l) H.nonneg H.lower (H.positive l) H.radius.le (H.root l) (H.source l) (H.frill l)
  simpa only [Poly.toll,Finset.prod_const_one,one_mul,amount,words,WilsonNeutralTwoPrintPathCensus.slates] using
    mul_le_mul_of_nonneg_left (add_le_add (le_refl (1:ℝ)) fare) (Real.exp_pos (σ*(B l).length)).le

end YM.Integration.WilsonReceivedDepositedOrbitalBudget
end
