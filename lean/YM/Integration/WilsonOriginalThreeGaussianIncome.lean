import YM.Integration.WilsonOriginalThreePurchasedRays
import YM.Integration.WilsonOriginalAllInputForestDriver
import YM.Integration.WilsonOriginalForestDriverReading
/-! All coefficients of the physical finite Gaussian generator at the first joint three-site hearing. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalThreeGaussianIncome
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
variable {G:Gauge} {n:Side} {I:Type} [Fintype I] {q:ℕ} {σ:ℝ}
  (owner:I→Fin 3) (grades:Fin 3→ℕ) (sites:Fin 3→Site n)
  (T:(l:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner l)) q σ) (A:Fin 3→Set ℂ) (charge:I→ℂ)
  (R:Run G) (N i per:ℕ) (hi:i<N) (F:Forest (step R i per).ratio) (tag:(step R i per).Choices)
  (h:n.val∣(fine R i per).val) (t:Wallet A) (L:Layout G) (tape:Finset Age)
  (Z:I→(m:Side)→Site m→PChart G m) (B:fieldDir G (coarse R i per) 1) (z:Precision.Key F G→ℝ)
local notation "M" => rows owner grades sites T A charge
local notation "J" => Stock.census (Fin 3)
local notation "Y" => copyColor h M grades (fun a=>(M a).paint t) L tape
local notation "U" => bank owner grades sites T A h t L tape
local notation "own" l:max => (T (l)).rows (home sites (owner (l))) (alone A (owner (l)))
local notation "S" => step R i per
local notation "D" => saddle R N i per F
local notation "K" => model R N i per hi


def value (r:ℕ)(s:Hot (Board (J) r)):ℂ:=
  let j:=(Join.right s.val).val.card
  (j.factorial:ℂ)*(if (Join.left s.val).val.Nonempty then
    ∑l:I,if (J).fire (owner l)=Join.left s.val then charge l*prescribed owner sites A R N i per hi F h t Z B z l j else 0
    else Cloud.paint z (SignedRegisteredMarkedProgram.register F B (coeff j (relative R N i per hi F (covered R N i per)))))

theorem original {w:Fin 3→ℝ}{σ₀ C:ℝ}{d seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ₀ C d seats shelf) (σpos:0<σ₀) (hs:0<σ) (bounded:∀v a,a∈A v→‖a‖≤1)
    (legal:Legal tape L) (shell:∀l m x,shellK (grades (owner l)) (Z l m x))
    (pure:∀l m x j,Pure (Z l m x j)) (matched:∀l,WilsonOriginalPrimerStampedRay.Matched (T l) (Z l))
    (e:ℕ)(quiet:SeriesA G)(r:ℕ)(hr:r≤q)(s:Hot (Board (J) r)):
    Cloud.paint z (driver R N i per hi F tag (Y) B e quiet r s)=
      value owner sites A charge R N i per hi F h t Z B z r s:=by
  have well:Bulk.Well (Y):=(copy_standard h M grades (fun a=>(M a).paint t) L tape
    (Air.license M _ grades w stock σpos (fun a=>stock.honor a t)) legal).1
  rw [WilsonOriginalForestDriverReading.original R N i per hi F tag (Y) B z e quiet well r s]
  unfold value
  by_cases use:(Join.left s.val).val.Nonempty
  · simp only [if_pos use,dif_pos use]
    apply congrArg (((Join.right s.val).val.card.factorial:ℂ)*·)
    exact WilsonOriginalThreePurchasedRays.original owner grades sites T A charge R N i per hi F tag h t L tape Z B z
      stock σpos hs bounded legal shell pure matched ⟨Join.left s.val,use⟩ _ ((Order.order_limit r (Join.right s.val)).trans hr)
  · simp only [if_neg use,dif_neg use]

end YM.Integration.WilsonOriginalThreeGaussianIncome
