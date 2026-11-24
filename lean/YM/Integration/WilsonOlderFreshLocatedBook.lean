import YM.Integration.WilsonOlderFreshLocatedFilm
import YM.Integration.WilsonOlderFreshPointDatedLedger

/-! One book at each actual site for both adjoining steps. Its physical
test follows the affine child pullback, including the full test jet. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOlderFreshLocatedBook
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

def word {n:Side}{σ:ℝ} (T:Copy G d Q σ)(site:Site n)(A:Unit→Set ℂ)(t:Wallet A)(g:ℝ)(V:Config G n):ℂ:=
  (Spill.Foundry.uncut (T.rows (WilsonOlderFreshGraphPointWallet.point site) A) g t V).part ((Stock.census Unit).fire ())

def fixed (σ:ℕ→ℝ)(T:∀j,m≤j→j≤N→axes→Studio D → Copy G d Q (σ j))
    (sites:∀j,Site (grid j))(f:ℕ→Studio D)(A:Unit→Set ℂ)(t:Wallet A)(g:ℕ→ℝ)
    (j:ℕ)(b:axes)(U:Config G (grid j)):ℂ:=
  if h:m≤j ∧ j≤N then word (T j h.1 h.2 b (f j)) (sites j) A t (g j) U else 0

theorem at_date (σ:ℕ→ℝ)(T:∀j,m≤j→j≤N→axes→Studio D → Copy G d Q (σ j))
    (sites:∀j,Site (grid j))(f:ℕ→Studio D)(A:Unit→Set ℂ)(t:Wallet A)(g:ℕ→ℝ)
    {j:ℕ}(lo:m≤j)(hi:j≤N)(b:axes):
    fixed R σ T sites f A t g j b=word (T j lo hi b (f j)) (sites j) A t (g j):=by
  funext U
  simp only [fixed,dif_pos (And.intro lo hi)]

def chart (digit:∀j,Site (R.family.S.block j))(first:ℕ)(f:Studio D):ℕ→Studio D
  | 0=>f
  | j+1=>Dawn.throughW (digit (first+j)) D (Elm.growL R.family.path.levels (first+j)) (chart digit first f j)

def orbit (digit:∀j,Site (R.family.S.block j))(first:ℕ)(f:Studio D)(j:ℕ):Studio D:=
  chart R digit first f (j-first)

theorem head (digit:∀j,Site (R.family.S.block j))(m:ℕ)(f:Studio D):orbit R digit m f m=f:=by
  simp only [orbit,Nat.sub_self,chart]

theorem next (digit:∀j,Site (R.family.S.block j)){m j:ℕ}(lo:m≤j)(f:Studio D):
    orbit R digit m f (j+1)=Dawn.throughW (digit j) D (Elm.growL R.family.path.levels j) (orbit R digit m f j):=by
  unfold orbit
  have diff:j+1-m=j-m+1:=by omega
  rw [diff,chart]
  exact congrArg (fun i=>Dawn.throughW (digit i) D (Elm.growL R.family.path.levels i) (chart R digit m f (j-m))) (Nat.add_sub_of_le lo)

theorem mass (digit:∀j,Site (R.family.S.block j))(m:ℕ)(f:Studio D)(j:ℕ):
    ‖orbit R digit m f j‖≤‖f‖:=by
  unfold orbit
  generalize j-m=k
  induction k with
  | zero=>exact le_rfl
  | succ k h=>
    exact (Dawn.through_le (digit (m+k)) (Elm.growL R.family.path.levels (m+k)) _).trans h

end YM.Integration.WilsonOlderFreshLocatedBook
end
