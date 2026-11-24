import YM.Integration.WilsonOlderFreshThermometerRoom
import YM.Integration.WilsonOriginalThreeCompactWallet
import YM.Integration.WilsonOriginalPointCompactVoter
import YM.Integration.WilsonOriginalCompactRafflePrice
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshThermometerCollector
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
variable {G:Gauge}(R:Run G)(L:Primer.Families R.family)(a:hue G){d D Q m N j:ℕ}
  (depth:d<D)(σ:ℕ → ℝ)(digit:∀l,Site (R.family.S.block l))
  (T:∀i,m ≤ i → i ≤ N → Letter (R.family.labels.level d) → Studio D → WilsonOlderFreshGraphSlate.Copy G d Q (σ i))

theorem enrolled (printed:Booked R L a depth Q σ m N digit T)(lo:m ≤ j)(hi:j ≤ N)(b:Letter (R.family.labels.level d))(f:Studio D):
    WilsonOlderFreshPointRegistry.Filed R L a depth (1/4) digit hi b f (T j lo hi b f):=
  printed.1 j lo hi b f

theorem entry (printed:Booked R L a depth Q σ m N digit T)(lo:m ≤ j)(hi:j ≤ N)(b:Letter (R.family.labels.level d))(f:Studio D):
    (∑z,(T j lo hi b f).fare z) ≤ R.alloy.B.a.clock.hatBeta j^((1:ℝ)/4)*(1+‖f‖):=
  (printed.1 j lo hi b f).1

section
variable {I:Type}[Fintype I]{q:ℕ}{width:ℝ}(owner:I → Fin 3)
  (copies:∀i,WilsonOlderFreshGraphSlate.Copy G (WilsonOlderFreshThermometerRoom.weight (owner i)) q width)
  (charge:I → ℂ)(test:I → ℝ)

def cap:ℝ:=∑i:I,‖charge i‖
def ticket (x:ℝ):ℝ:=x^((1:ℝ)/4)*(1+∑i:I,test i)

theorem actual {x:ℝ}(hx:0 ≤ x)(positive:∀i:I,0 ≤ test i)
    (fares:∀i:I,(∑z,(copies i).fare z) ≤ x^((1:ℝ)/4)*(1+test i)):
    0 ≤ ticket test x ∧ (∀i:I,‖charge i‖ ≤ cap charge) ∧
      (∀i:I,(∑z,(copies i).fare z) ≤ ticket test x) ∧
      (∑i:I,(1+‖charge i‖)*(∑z,(copies i).fare z)) ≤ ceiling I (cap charge) (ticket test x):=by
  have pos:0 ≤ ticket test x:=mul_nonneg (Real.rpow_nonneg hx _)
    (add_nonneg zero_le_one (Finset.sum_nonneg (fun t _=>positive t)))
  have owned(i:I):‖charge i‖ ≤ cap charge:=
    Finset.single_le_sum (fun w _=>norm_nonneg (charge w)) (Finset.mem_univ i)
  have due(i:I):(∑z,(copies i).fare z) ≤ ticket test x:=by
    have h:test i ≤ ∑w:I,test w:=Finset.single_le_sum (fun w _=>positive w) (Finset.mem_univ i)
    exact (fares i).trans (mul_le_mul_of_nonneg_left (by linarith : 1 + test i ≤ 1 + ∑ w:I,test w) (Real.rpow_nonneg hx _))
  exact ⟨pos,owned,due,WilsonOriginalPointCompactCash.bound owner WilsonOlderFreshThermometerRoom.weight copies charge due owned pos⟩
end

end YM.Integration.WilsonOlderFreshThermometerCollector
end
