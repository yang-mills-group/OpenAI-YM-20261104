import YM.Integration.WilsonOriginalCensusPaidForest

/-! The ordinary and connected readings use one funded forest for every
occupied component and its quiet normalization. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusGaussianTable
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
variable {G:Gauge} {n:Side} {V I:Type} [Fintype V] [DecidableEq V] [Fintype I]
  {P:Passport n V}(binders:I→Binder P (Stock.census V))(grades:V→ℕ)
  {q:ℕ}{σ:ℝ}(T:∀l,Copy G (∑v∈(binders l).mode.val,grades v) q σ)
  (R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  (h:n.val∣(fine R i per).val)(x:Wallet (room V))(L:Layout G)(tape:Finset Age)
  (Z:I→(n:Side)→Site n→PChart G n)
local notation "own" l:max => (T (l)).rows (WilsonOlderFreshGraphPointWallet.point (binders (l)).center) disk
local notation "M" => mounted binders (fun l=>own l)
local notation "J" => Stock.census V
local notation "joint" => copyColor h M grades (fun a=>(M a).paint x) L tape
local notation "S" => step R i per
local notation "saddle₀" => saddle R N i per F
local notation "K₀" => model R N i per hi

theorem original {w:V→ℝ}{σ₀ C:ℝ}{d seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ₀ C d seats shelf)(σpos:0<σ₀)(hs:0<σ)
    (legal:Legal tape L)(shell:∀l m y,shellK (∑v∈(binders l).mode.val,grades v) (Z l m y))
    (pure:∀l m y j,Pure (Z l m y j))(matched:∀l,WilsonOriginalPrimerStampedRay.Matched (T l) (Z l))
    {m e:ℕ}{quiet:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e quiet π Γ)(lo:m ≤ i){τ cash:ℝ}
    (funded:Issued R N (i+1) e (quiet (i+1)) τ cash)
    (b:Stationary.Link G (coarse R i per))(r:ℕ)(retained:r ≤ q)(grade:r ≤ e+2):
    let B₀:=Stationary.arm G _ 1 b
    let stockIn:=Bulk.Fk (K₀) F tag (QuadraticLocal.Fk.grant (π (i+1)) (Step.tape (e+2)) (joint)) B₀ r
    let income:=fun z=>WilsonOriginalCensusPaidForest.value binders R N i per hi F h x Z B₀ z r
    let Q₀:=(K₀).covariance F tag
    let computed:=WilsonOriginalGaussianPaidTable.table (Board (J) r) Q₀ income
    ratio stockIn=ratio computed ∧ logMarked stockIn=logMarked computed ∧
      ∀s,MeasureTheory.Integrable (WilsonOriginalGaussianPaidTable.presented (Board (J) r) income s) (Gaussian.cloud Q₀):=by
  intro B₀ stockIn income Q₀ computed
  have hit(z:Precision.Key F G→ℝ)(s:Hot (Board (J) r)):Cloud.paint z (driver R N i per hi F tag (joint) B₀ e (quiet (i+1)) r s)=income z s:=
    WilsonOriginalCensusPaidForest.original binders grades T R N i per hi F tag h x L tape Z B₀ z
      stock σpos hs legal shell pure matched e (quiet (i+1)) r retained s
  have read:=WilsonOriginalGaussianPaidTable.original (Board (J) r) Q₀ income ((K₀).symm F tag) ((K₀).positive F tag).posSemidef _ hit
  have joined:=WilsonOriginalAllInputForestDriver.original R N i per hi F tag (joint) course lo funded b r grade
  exact ⟨joined.1.trans (congrArg Order.ratio read.1),joined.2.trans (congrArg Order.logMarked read.1),read.2⟩

end YM.Integration.WilsonOriginalCensusGaussianTable
end
