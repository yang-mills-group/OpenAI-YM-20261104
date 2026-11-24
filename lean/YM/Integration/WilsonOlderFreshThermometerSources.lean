import YM.Integration.WilsonOlderFreshThermometerCollector

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshThermometerSources
open OPE.Therm
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

abbrev Table := ∀v,∀i,m ≤ i → i ≤ N → Letter (R.family.labels.level (WilsonOlderFreshThermometerRoom.weight v)) → Studio (dmax v) →
  WilsonOlderFreshGraphSlate.Copy G (WilsonOlderFreshThermometerRoom.weight v) Q (σ i)

variable (T:Table (m:=m) (N:=N) (Q:=Q) R dmax σ)(lo:m ≤ j)(hi:j ≤ N)
    {I:Type}[Fintype I](owner:I → Fin 3)
    (columns:∀i,Letter (R.family.labels.level (WilsonOlderFreshThermometerRoom.weight (owner i))))(films:∀i,Studio (dmax (owner i)))
    (charge:I → ℂ)

def selected (i:I):WilsonOlderFreshGraphSlate.Copy G (WilsonOlderFreshThermometerRoom.weight (owner i)) Q (σ j):=
  T (owner i) j lo hi (columns i) (films i)

local notation "T₁" => selected R dmax σ T lo hi owner columns films
local notation "profile" => (fun i:I=>‖films i‖)
local notation "xj" => R.alloy.B.a.clock.hatBeta j
def Sold:Prop:=∀v,Booked R L a (depth v) Q σ m N (digit v) (T v)

theorem original (issued:Sold R L a dmax depth σ digit T):
    (∀i:I, WilsonOlderFreshPointRegistry.Filed R L a (depth (owner i)) (1/4) (digit (owner i))
      hi (columns i) (films i) (T₁ i)) ∧
    0 ≤ ticket profile xj ∧ (∀i:I,‖charge i‖ ≤ cap charge) ∧
    (∀i:I,(∑z,(T₁ i).fare z) ≤ ticket profile xj) ∧
    (∑i:I,(1+‖charge i‖)*(∑z,(T₁ i).fare z)) ≤ WilsonOriginalPointCompactCash.ceiling I (cap charge) (ticket profile xj):=by
  have paid(i:I):WilsonOlderFreshPointRegistry.Filed R L a (depth (owner i)) (1/4) (digit (owner i))
      hi (columns i) (films i) (T₁ i):= (issued (owner i)).1 j lo hi (columns i) (films i)
  have pos:0 ≤ xj:= (zero_lt_one.trans (R.alloy.B.a.fits.delayed j)).le
  exact ⟨paid,WilsonOlderFreshThermometerCollector.actual owner (T₁) charge profile pos
    (fun i=>norm_nonneg _) (fun i=>(paid i).1)⟩

end YM.Integration.WilsonOlderFreshThermometerSources
end
