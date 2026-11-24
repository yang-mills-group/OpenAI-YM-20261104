import YM.Integration.WilsonWeakBinaryGaussianColors

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonWeakBinaryGaussian
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
variable {G:Gauge} {I:Type} [Fintype I] {q:ℕ} {σ:ℝ}
  (R:Run G) (N i per:ℕ) (hi:i<N) (F:Forest (step R i per).ratio) (tag:(step R i per).Choices)
  (owner:I→Fin 3) (grades:Fin 3→ℕ) (sites:Fin 3→Site (fine R i per))
  (T:(l:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner l)) q σ) (A:Fin 3→Set ℂ) (charge:I→ℂ)
  (t:Wallet A) (Z:I→(m:Side)→Site m→PChart G m)
local notation "M" => rows owner grades sites T A charge
local notation "J" => Stock.census (Fin 3)
local notation "K" => model R N i per hi


theorem original {w:Fin 3→ℝ}{σ₀ C:ℝ}{d seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ₀ C d seats shelf) (σpos:0<σ₀) (hs:0<σ) (bounded:∀v a,a∈A v→‖a‖≤1)
    {m e:ℕ}{quiet:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (legal:Legal (Step.tape (e+2)) (π (i+1))) (shell:∀l m x,shellK (grades (owner l)) (Z l m x))
    (pure:∀l m x j,Pure (Z l m x j)) (matched:∀l,WilsonOriginalPrimerStampedRay.Matched (T l) (Z l))

    (course:Read R N m e quiet π Γ)(lo:m ≤ i){τ cash:ℝ}
    (funded:Issued R N (i+1) e (quiet (i+1)) τ cash)
    (b:Stationary.Link G (coarse R i per))(r:ℕ)(retained:r ≤ q)(grade:r ≤ e+2):
    let B₀:=Stationary.arm G _ 1 b
    let stockIn:=Bulk.Fk (K) F tag (Air.craft M (fun a=>(M a).paint t) grades (π (i+1)) (Step.tape (e+2))) B₀ r
    let income:=fun z=>WilsonOriginalThreeGaussianIncome.value owner sites A charge R N i per hi F (dvd_refl _) t Z B₀ z r
    let Q₀:=(K).covariance F tag
    let computed:=WilsonOriginalGaussianPaidTable.table (Board (J) r) Q₀ income
    ratio stockIn=ratio computed ∧ logMarked stockIn=logMarked computed ∧
      ∀s,MeasureTheory.Integrable (WilsonOriginalGaussianPaidTable.presented (Board (J) r) income s) (Gaussian.cloud Q₀):=by
  intro B₀ stockIn income Q₀ computed
  have same:=WilsonWeakBinaryGaussianColors.original M grades (fun z=>(M z).paint t) (π (i+1)) (Step.tape (e+2))
  dsimp only [stockIn]
  rw [same]
  exact WilsonOriginalThreeGaussianReturn.original owner grades sites T A charge R N i per hi F tag (dvd_refl _) t
    (π (i+1)) (Step.tape (e+2)) Z stock σpos hs bounded legal shell pure matched course lo funded b r retained grade

end YM.Integration.WilsonWeakBinaryGaussian
end
