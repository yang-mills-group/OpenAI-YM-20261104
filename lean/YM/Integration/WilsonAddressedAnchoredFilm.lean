import YM.Integration.WilsonOlderFreshLocatedBook
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonAddressedAnchoredFilm
open Lattice Marker RG QuadraticLocal QuadraticLocal.Affinity Wilson FormalBulk08 City Pose
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
open WilsonEmittedOriginalReturn Push.AbsoluteSums Extra.Histories Extra.Histories.Relay
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker
open MeasureTheory
open WilsonOlderFreshGraphSlate
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {D d Q N per m:ℕ}
local notation "axes" => Letter (R.family.labels.level d)
local notation "grid" j:max => R.family.side j per


def anchored (D:ℕ)(c:ℝ):Studio D:=Dawn.portrait D ⟨fun _=>c,(contDiff_const : ContDiff ℝ D (fun _:E4=>c))⟩

theorem unchanged {L:Side}(w:Site L)(D:ℕ)(c:ℝ)(h:2≤L.val):
    Dawn.throughW w D h (anchored D c)=anchored D c:=by
  rw [anchored,Dawn.through_show]
  rfl

theorem constant_chart (digit:∀j,Site (R.family.S.block j))(first D:ℕ)(c:ℝ)(j:ℕ):
    WilsonOlderFreshLocatedBook.chart R digit first (anchored D c) j=anchored D c:=by
  induction j with
  | zero=>rfl
  | succ j ih=>rw [WilsonOlderFreshLocatedBook.chart,ih,unchanged]

theorem constant_orbit (digit:∀j,Site (R.family.S.block j))(first D:ℕ)(c:ℝ)(j:ℕ):
    WilsonOlderFreshLocatedBook.orbit R digit first (anchored D c) j=anchored D c:=
  constant_chart R digit first D c (j-first)

theorem original (σ:ℕ→ℝ)(T:∀j,m≤j→j≤N→axes→Studio D → Copy G d Q (σ j))
    (digit center:∀j,Site (R.family.S.block j))(sites placed:∀j,Site (grid j))
    (first second:ℕ)(c:ℝ)(A:Unit→Set ℂ)(t:Wallet A)(g:ℕ→ℝ){s:ℕ}(ms:m ≤ s)(sn:s≤N)
    (inCommon:sites s=placed s)(b:axes):
    WilsonOlderFreshLocatedBook.fixed R σ T sites (WilsonOlderFreshLocatedBook.orbit R digit first (anchored D c)) A t g s b=
      WilsonOlderFreshLocatedBook.fixed R σ T placed (WilsonOlderFreshLocatedBook.orbit R center second (anchored D c)) A t g s b:=by
  rw [WilsonOlderFreshLocatedBook.at_date R _ _ _ _ _ _ _ ms sn,
      WilsonOlderFreshLocatedBook.at_date R _ _ _ _ _ _ _ ms sn,
      constant_orbit,constant_orbit,inCommon]

end YM.Integration.WilsonAddressedAnchoredFilm
end
