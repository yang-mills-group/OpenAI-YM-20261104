import YM.Integration.WilsonOriginalCensusPageRays
import YM.Integration.WilsonOriginalGaussianPaidTable
import YM.Integration.WilsonOriginalThreeGaussianReturn

/-! The finite Gaussian driver on the deposited branch roster. Each original mode uses
its whole copied word at its own deposited site and at its actual source degree. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusWickPages
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
  {q:ℕ}{σ:ℝ}(T:∀l,Copy G (∑v∈(binders l).mode.val,grades v) q σ)
  (R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  (h:n.val∣(fine R i per).val)(x:Wallet (room V))(L:Layout G)(tape:Finset Age)
  (Z:I→(n:Side)→Site n→PChart G n)(B:fieldDir G (coarse R i per) 1)(z:Precision.Key F G→ℝ)
local notation "own" l:max => (T (l)).rows (WilsonOlderFreshGraphPointWallet.point (binders (l)).center) disk
local notation "M" => mounted binders (fun l=>own l)
local notation "J" => Stock.census V
local notation "joint" => copyColor h M grades (fun a=>(M a).paint x) L tape
local notation "S" => step R i per
local notation "saddle₀" => saddle R N i per F
local notation "K₀" => model R N i per hi

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
local notation "full" => WilsonOriginalCensusPaidForest.value binders R N i per hi F h x Z B z

def entry {r:ℕ}(s:Hot (Board J r))(u:whereFrom):ℂ:=
  let j:=(Join.right s.val).val.card
  match u with
  | none=>if (Join.left s.val).val.Nonempty then 0 else full r s
  | some (l,p)=>if (Join.left s.val).val.Nonempty ∧ (binders l).mode=Join.left s.val then
      (j.factorial:ℂ)*atLift binders R N i per hi F h x Z B z l p j else 0

theorem bill (shell:∀l a,shellK (∑v∈(binders l).mode.val,grades v) (Z l (fine R i per) a))
    (pure:∀l a j,Pure (Z l (fine R i per) a j))
    {r:ℕ}(s:Hot (Board J r)):
    full r s=∑a,entry binders R N i per hi F h x Z B z s a:=by
  classical
  rw [Fintype.sum_option]
  simp only [Fintype.sum_prod_type,entry]
  by_cases used:(Join.left s.val).val.Nonempty
  · simp only [used,if_true,zero_add,true_and]
    simp only [WilsonOriginalCensusPaidForest.value,used,if_true,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    by_cases belongs:(binders l).mode=Join.left s.val
    · simp only [belongs,if_true,←Finset.mul_sum]
      rw [WilsonOriginalCensusPageRays.pages binders R N i per hi F h x Z B z l
        (Join.right s.val).val.card _ (shell l) (pure l)]
    · simp [belongs]
  · simp [used]

/-- Within each actual shard each marked item has its own upper page. Quiet thermal
items have a unique surviving address and use the deposited quiet measure unchanged. -/
theorem ordinary (shell:∀l a,shellK (∑v∈(binders l).mode.val,grades v) (Z l (fine R i per) a))
    (pure:∀l a j,Pure (Z l (fine R i per) a j))
    (r:ℕ)(s:(Board J r).Mode):
    presented (Board J r) (fun zz=>WilsonOriginalCensusPaidForest.value binders R N i per hi F h x Z B zz r) s z=
      ∑Q∈shards (Board J r) s,∑p:Q.val → whereFrom,
        ∏t:Q.val,entry binders R N i per hi F h x Z B z t.val (p t):=by
  classical
  unfold presented
  rw [pass_partition _ (part_lit_quiet _)]
  apply Finset.sum_congr rfl
  intro Q _
  simp only [part_lit]
  rw [←Finset.prod_attach Q.val (fun t:Hot (Board J r)=>full r t)]
  simp_rw [bill binders grades R N i per hi F h x Z B z shell pure]
  exact Fintype.prod_sum _

end YM.Integration.WilsonOriginalCensusWickPages
end
