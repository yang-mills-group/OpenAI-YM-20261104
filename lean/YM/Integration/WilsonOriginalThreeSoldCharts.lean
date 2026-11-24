import YM.Integration.WilsonOlderFreshThermometerSources

/-! Actual chart receipts of the three selected point sources, in their own original periods. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalThreeSoldCharts
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology


open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open WilsonOlderFreshGraphPainter
open WilsonOriginalReceivedChain WilsonMeasuredRankedResidual Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle QuadraticLocal.Earn Primitives.TwoWave
open WilsonNeutralRenderedColumn WilsonOriginalPrimerFiledPages
open WilsonMeasuredTransitionCatalogue
open WilsonMeasuredOriginalCatalogueUnion WilsonEmittedFiledGerm
open QuadraticLocal.Earn
open WilsonMeasuredJointCensusCash
open WilsonEmittedDictionary Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open WilsonLimitConstruction.FundedDictionaryPatchPrices
open WilsonEmittedOriginalReturn Push.AbsoluteSums
open WilsonOlderFreshPointRegistry

open MeasureTheory WilsonOlderFreshLocatedBook WilsonOlderFreshLocatedPayment
open WilsonOlderFreshLocatedRoster WilsonMeasuredPointHouseSeats
open WilsonOlderFreshGraphAllStages QuadraticLocal.Advent.Sycamore
open WilsonWindowBookPurchase WilsonWindowUniversalSchool
open scoped Classical BigOperators
open WilsonOlderFreshThermometerRoom WilsonOriginalPointCompactRoster WilsonOriginalPointCompactCash
open WilsonOlderFreshLocatedRoster WilsonOlderFreshPointRegistry

open WilsonOlderFreshThermometerCollector
variable {G:Gauge}(R:Run G)(L:Primer.Families R.family)(a:hue G){Q m N j:ℕ}
    (dmax:Fin 3 → ℕ)(depth:∀v,WilsonOlderFreshThermometerRoom.weight v<dmax v)(σ:ℕ → ℝ)(digit:Fin 3 → ∀i,Site (R.family.S.block i))

variable (T:WilsonOlderFreshThermometerSources.Table (m:=m) (N:=N) (Q:=Q) R dmax σ)(lo:m ≤ j)(hi:j ≤ N)
    {I:Type}[Fintype I](owner:I → Fin 3)
    (columns:∀i,Letter (R.family.labels.level (WilsonOlderFreshThermometerRoom.weight (owner i))))(films:∀i,Studio (dmax (owner i)))
    


local notation "T₁" => WilsonOlderFreshThermometerSources.selected R dmax σ T lo hi owner columns films
def charts (l:I):=
  WilsonOlderFreshPointChart.chart R L a (depth (owner l)) j (columns l) (⟨N,hi,digit (owner l)⟩,films l)
local notation "Z₁" => charts R L a dmax depth digit hi owner columns films

omit [Fintype I] in
theorem original (sold:WilsonOlderFreshThermometerSources.Sold R L a dmax depth σ digit T):
    (∀l n x,WilsonCoeffUV.Blue.shellK (weight (owner l)) (Z₁ l n x)) ∧
    (∀l n x q,WilsonCoeffUV.Blue.Pure (Z₁ l n x q)) ∧
    (∀l,WilsonOriginalPrimerStampedRay.Matched (T₁ l) (Z₁ l)):=by
  have admitted(l:I)(n:Side)(x:Site n):=WilsonOlderFreshPointChart.admitted R L a (depth (owner l)) j
    (columns l) (⟨N,hi,digit (owner l)⟩,films l) n x
  refine ⟨fun l n x=>(admitted l n x).1,fun l n x q=>(admitted l n x).2 q,?_⟩
  intro l
  exact ((sold (owner l)).1 j lo hi (columns l) (films l)).2.2

end YM.Integration.WilsonOriginalThreeSoldCharts
