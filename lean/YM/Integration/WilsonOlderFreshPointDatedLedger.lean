import YM.Integration.WilsonMeasuredPointQueryCalendar
import YM.Integration.WilsonOlderFreshPointNeighbours

/-! File a single lower marked table on both adjoining edges before fixing either physical regulator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointDatedLedger
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
variable {G:Gauge} (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
variable {k:ℕ} (school:Syl.School k) (q:ℕ)(query:WilsonOlderFreshGraphAllStages.Query)(high:ℕ) {ε:ℝ} (ep:0<ε)
local notation "q₁" => (q+2+2)
local notation "target" d:max q:max => 2*4+(d+1)+1+(q+3)
private theorem micro {ε:ℝ} (ep:0<ε):0<(ε/8)/16:=by positivity
local notation "ep₀" => micro ep
private theorem ready_order {q J:ℕ} (h:2*(q+4+1)+8 ≤ J):2*q+8 ≤ J:=by omega
private theorem ready_age {q k:ℕ} (h:q+4+4 ≤ 3*k+2):q+3 ≤ 3*k+2:=by omega
variable (deep:2*((q+2+2)+4+1)+8 ≤ school.order)(aged:(q+2+2)+4+4 ≤ 3*k+2)
variable (tube:LinkTube G)(programPaid:Covered (program tube) R)
  (strength:∀ i,(R.family.path.levels.budget i).supportExponent ≤ 100)
  (enough:3*(target query.letter.toll q) ≤ query.order)
  (prepared:WilsonReportLampForecast.Ready R.family.path.levels)
  (M₀:WilsonMeasuredRankedMenu.Menu R query.letter.toll)


open WilsonNeutralPointCourse WilsonOlderFreshPointRegistry
variable (L:Primer.Families R.family)(a:hue G){D:ℕ}(depth:query.letter.toll<D)
variable (seed:ℕ→ℕ→ℝ)

local notation "calendar" => WilsonMeasuredPointQueryCalendar.Dated R simple slow school q query high ep tube programPaid strength enough prepared M₀ deep aged

include deep aged in
theorem original (ledger:WilsonOlderFreshPointHouseRegistry.Ledger R L a depth query.order seed (1/4)):
    ∀ᶠ m:ℕ in atTop,∀(N:ℕ)(digit:∀j,Site (R.family.S.block j)),
      k ≤ R.alloy.B.a.clock.J m→1 ≤ Burn.horizon k→
      let σ:=fun j=>seed (Burn.horizon k) (R.alloy.B.a.clock.J j)
      ∃T:∀j,m ≤ j→j ≤ N→Letter (R.family.labels.level query.letter.toll)→Studio D→
        WilsonOlderFreshGraphSlate.Copy G query.letter.toll query.order (σ j),
        ∀j (lo:m ≤ j)(hi:j+1<N)(w:Letter (R.family.labels.level query.letter.toll))(f:Studio D),
          let h:=lo.trans (Nat.le_succ j)
          let g:=Dawn.throughW (digit (j+1)) D (Elm.growL R.family.path.levels (j+1)) f
          let H:=T ((j+1)+1) (h.trans (Nat.le_succ _)) hi w g
          let T₀:=fun u=>T (j+1) h hi.le u f
          let μ:=fun u (ν:Fin (query.order+1))=>|PowerSeries.coeff ν.val (transfer R L a depth digit N (j+1) u w)|
          (calendar j) ∧
            Filed R L a depth (1/4) digit hi w g H ∧
            (∑x,H.fare x) ≤ (R.alloy.B.a.clock.hatBeta ((j+1)+1))^((1:ℝ)/2)*(1+‖g‖) ∧
            (∀u,Filed R L a depth (1/4) digit hi.le u f (T₀ u)) ∧
            (∀u,(∑x,(T₀ u).fare x) ≤ R.alloy.B.a.clock.hatBeta (j+1)*(1+‖f‖)) ∧
            (∑u,∑ν,μ u ν) ≤ R.alloy.B.a.clock.hatBeta (j+1) ∧
            (∑u,∑ν,μ u ν*(∑x,(T₀ u).fare x)) ≤ R.alloy.B.a.clock.hatBeta (j+1)^((1:ℝ)/2)*(1+‖f‖):=by
  obtain ⟨first,sold⟩:= WilsonOlderFreshPointNeighbours.original R L a depth query.order seed ledger
  obtain ⟨start,age⟩:=eventually_atTop.mp (WilsonMeasuredPointQueryCalendar.funded R simple slow school q query high ep
    deep aged tube programPaid strength enough prepared M₀)
  filter_upwards [eventually_ge_atTop first,eventually_ge_atTop start] with m issued late
  intro N digit floor duty
  obtain ⟨T,orders⟩:=sold m issued N k digit floor duty
  exact ⟨T,fun j lo hi w f=>⟨age j (late.trans lo),orders (j+1) (lo.trans (Nat.le_succ j)) hi w f⟩⟩

end YM.Integration.WilsonOlderFreshPointDatedLedger
end
