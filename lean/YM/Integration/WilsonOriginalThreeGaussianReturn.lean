import YM.Integration.WilsonOriginalThreeGaussianIncome
import YM.Integration.WilsonOriginalGaussianPaidTable
/-! The true first finite three-source return on the same measured vacuum and Gaussian law. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalThreeGaussianReturn
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
variable {G:Gauge} {n:Side} {I:Type} [Fintype I] {q:ℕ} {σ:ℝ}
  (owner:I→Fin 3) (grades:Fin 3→ℕ) (sites:Fin 3→Site n)
  (T:(l:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner l)) q σ) (A:Fin 3→Set ℂ) (charge:I→ℂ)
  (R:Run G) (N i per:ℕ) (hi:i<N) (F:Forest (step R i per).ratio) (tag:(step R i per).Choices)
  (h:n.val∣(fine R i per).val) (t:Wallet A) (L:Layout G) (tape:Finset Age)
  (Z:I→(m:Side)→Site m→PChart G m) (B:fieldDir G (coarse R i per) 1)
local notation "M" => rows owner grades sites T A charge
local notation "J" => Stock.census (Fin 3)
local notation "Y" => copyColor h M grades (fun a=>(M a).paint t) L tape
local notation "U" => bank owner grades sites T A h t L tape
local notation "own" l:max => (T (l)).rows (home sites (owner (l))) (alone A (owner (l)))
local notation "S" => step R i per
local notation "D" => saddle R N i per F
local notation "K" => model R N i per hi


theorem original {w:Fin 3→ℝ}{σ₀ C:ℝ}{d seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ₀ C d seats shelf) (σpos:0<σ₀) (hs:0<σ) (bounded:∀v a,a∈A v→‖a‖≤1)
    (legal:Legal tape L) (shell:∀l m x,shellK (grades (owner l)) (Z l m x))
    (pure:∀l m x j,Pure (Z l m x j)) (matched:∀l,WilsonOriginalPrimerStampedRay.Matched (T l) (Z l))
   
    {m e:ℕ}{quiet:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e quiet π Γ)(lo:m ≤ i){τ cash:ℝ}
    (funded:Issued R N (i+1) e (quiet (i+1)) τ cash)
    (b:Stationary.Link G (coarse R i per))(r:ℕ)(retained:r ≤ q)(grade:r ≤ e+2):
    let B₀:=Stationary.arm G _ 1 b
    let stockIn:=Bulk.Fk (K) F tag (QuadraticLocal.Fk.grant (π (i+1)) (Step.tape (e+2)) (Y)) B₀ r
    let income:=fun z=>WilsonOriginalThreeGaussianIncome.value owner sites A charge R N i per hi F h t Z B₀ z r
    let Q₀:=(K).covariance F tag
    let computed:=WilsonOriginalGaussianPaidTable.table (Board (J) r) Q₀ income
    ratio stockIn=ratio computed ∧ logMarked stockIn=logMarked computed ∧
      ∀s,MeasureTheory.Integrable (WilsonOriginalGaussianPaidTable.presented (Board (J) r) income s) (Gaussian.cloud Q₀):=by
  intro B₀ stockIn income Q₀ computed
  have hit(z:Precision.Key F G→ℝ)(s:Hot (Board (J) r)):Cloud.paint z (driver R N i per hi F tag (Y) B₀ e (quiet (i+1)) r s)=income z s:=
    WilsonOriginalThreeGaussianIncome.original owner grades sites T A charge R N i per hi F tag h t L tape Z B₀ z
      stock σpos hs bounded legal shell pure matched e (quiet (i+1)) r retained s
  have read:=WilsonOriginalGaussianPaidTable.original (Board (J) r) Q₀ income ((K).symm F tag) ((K).positive F tag).posSemidef _ hit
  have joined:=WilsonOriginalAllInputForestDriver.original R N i per hi F tag (Y) course lo funded b r grade
  exact ⟨joined.1.trans (congrArg Order.ratio read.1),joined.2.trans (congrArg Order.logMarked read.1),read.2⟩

end YM.Integration.WilsonOriginalThreeGaussianReturn
