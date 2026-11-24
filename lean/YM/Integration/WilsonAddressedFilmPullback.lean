import YM.Integration.WilsonAddressedAnchoredFilm
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonAddressedFilmPullback
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



def stretch (first:ℕ):ℕ→ℝ
  | 0=>1
  | j+1=>stretch first j*Dawn.scale (R.family.S.block (first+j))

def displacement (digit:∀j,Site (R.family.S.block j))(first:ℕ):ℕ→E4
  | 0=>0
  | j+1=>displacement digit first j+stretch R first j • Dawn.pith (digit (first+j))

def window {D:ℕ}(f:Garden D)(v:E4)(α:ℝ):Garden D:=
  ⟨fun x=>f.val (v+α • x),by
    change ContDiff ℝ D (f.val ∘ fun x=>v+α • x)
    exact (show ContDiff ℝ D f.val from f.property).comp (by fun_prop)⟩

theorem bowl {D:ℕ}{L:Side}(f:Garden D)(x:Site L)(v:E4)(α:ℝ):
    Dawn.bowl x (window f v α)=window f (v+α • Dawn.pith x) (α*Dawn.scale L):=by
  apply Subtype.ext
  funext y
  change f.val (v+α • (Dawn.pith x+Dawn.scale L • y))=f.val ((v+α • Dawn.pith x)+(α*Dawn.scale L) • y)
  simp only [smul_add,smul_smul,add_assoc]

theorem chart {D:ℕ}(digit:∀j,Site (R.family.S.block j))(first:ℕ)(f:Garden D)(j:ℕ):
    WilsonOlderFreshLocatedBook.chart R digit first (Dawn.portrait D f) j =
      Dawn.portrait D (window f (displacement R digit first j) (stretch R first j)):=by
  induction j with
  | zero=>
    change Dawn.portrait D f=Dawn.portrait D (window f 0 1)
    apply congrArg
    apply Subtype.ext
    funext y
    change f.val y=f.val (0+(1:ℝ) • y)
    simp
  | succ j ih=>
    rw [WilsonOlderFreshLocatedBook.chart,ih,Dawn.through_show,bowl]
    rfl

theorem orbit {D:ℕ}(digit:∀j,Site (R.family.S.block j))(m:ℕ)(f:Garden D)(s:ℕ):
    WilsonOlderFreshLocatedBook.orbit R digit m (Dawn.portrait D f) s=
      Dawn.portrait D (window f (displacement R digit m (s-m)) (stretch R m (s-m))):=
  chart R digit m f (s-m)

def refocus {D:ℕ}(digit center:∀j,Site (R.family.S.block j))(m s:ℕ)(f:Garden D):Garden D:=
  window f (displacement R digit m (s-m)-displacement R center m (s-m)) 1

theorem registered {D:ℕ}(digit center:∀j,Site (R.family.S.block j))(m s:ℕ)(f:Garden D):
    WilsonOlderFreshLocatedBook.orbit R digit m (Dawn.portrait D f) s =
      WilsonOlderFreshLocatedBook.orbit R center m (Dawn.portrait D (refocus R digit center m s f)) s:=by
  rw [orbit,orbit]
  apply congrArg
  apply Subtype.ext
  funext y
  change f.val (displacement R digit m (s-m)+stretch R m (s-m) • y)=
    f.val ((displacement R digit m (s-m)-displacement R center m (s-m))+
      (1:ℝ) • (displacement R center m (s-m)+stretch R m (s-m) • y))
  rw [one_smul];abel_nf

theorem linear {D:ℕ}(digit:∀j,Site (R.family.S.block j))(m s:ℕ)(f g:Studio D):
    WilsonOlderFreshLocatedBook.orbit R digit m (f-g) s=
      WilsonOlderFreshLocatedBook.orbit R digit m f s-WilsonOlderFreshLocatedBook.orbit R digit m g s:=by
  suffices H:∀j:ℕ,WilsonOlderFreshLocatedBook.chart R digit m (f-g) j=
      WilsonOlderFreshLocatedBook.chart R digit m f j-WilsonOlderFreshLocatedBook.chart R digit m g j from H (s-m)
  intro j
  induction j with
  | zero=>rfl
  | succ j ih=>
    simp only [WilsonOlderFreshLocatedBook.chart,ih,map_sub]

theorem compensated {D:ℕ}(digit center:∀j,Site (R.family.S.block j))(m s:ℕ)(f g:Garden D):
    WilsonOlderFreshLocatedBook.orbit R digit m (Dawn.portrait D f) s-
      WilsonOlderFreshLocatedBook.orbit R center m (Dawn.portrait D g) s=
      WilsonOlderFreshLocatedBook.orbit R center m
        (Dawn.portrait D (refocus R digit center m s f)-Dawn.portrait D g) s:=by
  rw [linear,registered R digit center]

end YM.Integration.WilsonAddressedFilmPullback
end
