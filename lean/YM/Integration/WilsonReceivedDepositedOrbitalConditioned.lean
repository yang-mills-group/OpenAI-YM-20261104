import YM.Integration.WilsonReceivedDepositedOrbitalIntegral
import YM.Integration.WilsonReceivedDepositedOrbitalPaint

/-! Relabel the actual connected pieces only after the entire fixed-period conditional
Gaussian has been formed. Every coupling coefficient is divided by the same finite
unmarked denominator, including the inherited nonbare thermal terms. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalConditioned
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
open WilsonOriginalThreePurchasedRays (prescribed)
attribute [local instance] Gauge.frobInner
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet WilsonOriginalCensusCopySlate
open WilsonOlderFreshGraphSlate (Copy)
variable {G:Gauge} {n:Side} {V I:Type} [Fintype V] [DecidableEq V] [Fintype I]
  {P:Passport n V}(binders:I→Binder P (Stock.census V))(grades:V→ℕ)
  (R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  (h:n.val∣(fine R i per).val)(x:Wallet (room V))
  (Z:I→(n:Side)→Site n→PChart G n)(B:fieldDir G (coarse R i per) 1)(z:Precision.Key F G→ℝ)
local notation "J" => Stock.census V
open Function Finset Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Blue.Cameo Marker QuadraticLocal QuadraticLocal.Earn FVA1Physical.TwoReset PowerSeries
open scoped Classical BigOperators


open WilsonOriginalCensusPaidForest (ray)
open WilsonOriginalFoldedMarkedRightColumn (before)
open WilsonOriginalCensusPageRays (atLift)
open WilsonOriginalGaussianPaidTable (presented)
open MeasureTheory YM.Comparison.RG02.Cumulants

local notation "finePage" => Fin (Pages n (fine R i per))
local notation "whereFrom" => Option (I × finePage)
local notation "full" a:max => WilsonOriginalCensusPaidForest.value binders R N i per hi F h x Z B a


open WilsonReceivedDepositedOrbitalSlice WilsonReceivedDepositedOrbitalMonomials


open WilsonReceivedDepositedOrbitalPhases
open WilsonReceivedDepositedOrbitalIntegral (take integrated)
local notation "S₁" => Stock.census (I×finePage)
local notation "Q₀" => (model R N i per hi).covariance F tag
local notation "μ₀" => Gaussian.cloud (Q₀)
local notation "φ₀" => WilsonReceivedDepositedAlias.fold (J) (name binders R i per)

def staged (r:ℕ):Grade (S₁) r:=
  take (μ₀) (fun z=>(temporary binders R N i per hi F h x Z B z r).pass)

theorem accepts (r:ℕ):UnitLeading (staged binders R N i per hi F tag h x Z B r):=by
  change (∫z,((temporary binders R N i per hi F h x Z B z r).pass).part (Board (S₁) r).quiet ∂(μ₀))=1
  simp_rw [Poly.pass_part _ (WilsonReceivedDepositedOrbitalPaint.zero binders R N i per hi F h x Z B _ r)]
  simp

theorem before (shell:∀l a,shellK (∑v∈(binders l).mode.val,grades v) (Z l (fine R i per) a))
    (pure:∀l a j,Pure (Z l (fine R i per) a j))(r:ℕ):
    hom (φ₀) r (staged binders R N i per hi F tag h x Z B r)=
      WilsonOriginalGaussianPaidTable.table (Board (J) r) (Q₀) (fun z=>(full z) r):=by
  let temp:=fun z=>temporary binders R N i per hi F h x Z B z r
  have phase(z):hom (φ₀) r (temp z).pass=Poly.pass (lit (Board (J) r) ((full z) r)):=by
    have actual:=WilsonReceivedDepositedOrbitalPhases.original binders grades R N i per hi F h x Z B z shell pure r
    have flat:=WilsonReceivedDepositedOrbitalPaint.zero binders R N i per hi F h x Z B z r
    have flat₂:(hom (φ₀) r (temp z)).part (Board (J) r).quiet=0:=
      (WilsonReceivedDepositedOrbitalThermals.vacant (φ₀) (WilsonReceivedDepositedOrbitalThermals.original_quiet _ _) (temp z)).trans flat
    exact (pass_map (hom (φ₀) r) (temp z) flat flat₂).trans (congrArg Poly.pass actual)
  unfold staged
  rw [integrated _ (μ₀) _ (WilsonReceivedDepositedOrbitalPaint.original binders R N i per hi F h x Z B tag r)]
  change take (μ₀) (fun z=>hom (φ₀) r (temp z).pass)=_
  rw [funext phase]
  rfl

theorem original (shell:∀l a,shellK (∑v∈(binders l).mode.val,grades v) (Z l (fine R i per) a))
    (pure:∀l a j,Pure (Z l (fine R i per) a j))(r coupling:ℕ):
    let stock:=WilsonOriginalGaussianPaidTable.table (Board (J) r) (Q₀) (fun z=>(full z) r)
    let joint:=staged binders R N i per hi F tag h x Z B r
    Order.observe (J) r (Order.ratio stock) coupling=(φ₀) (Order.observe (S₁) r (Order.ratio joint) coupling) ∧
    Order.observe (J) r (Order.logMarked stock) coupling=(φ₀) (Order.observe (S₁) r (Order.logMarked joint) coupling):=by
  dsimp only
  rw [←before binders grades R N i per hi F tag h x Z B shell pure r]
  exact WilsonReceivedDepositedOrbitalThermals.original (J) (name binders R i per) _
    (accepts binders R N i per hi F tag h x Z B r) coupling

end YM.Integration.WilsonReceivedDepositedOrbitalConditioned
end
