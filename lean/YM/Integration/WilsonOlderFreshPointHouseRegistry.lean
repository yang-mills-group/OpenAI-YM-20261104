import YM.Integration.WilsonOlderFreshPointSchool
import YM.Integration.WilsonOlderFreshPointRegistry
import YM.Integration.WilsonOlderFreshPointMatrixCash
import YM.Integration.WilsonNeutralPointWeakIncome
/-! The common original school supplies one pointed word per date,
basis vector and film, reused on adjacent edges of each finite history.
Both weak prices are produced on the same original run before the cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointHouseRegistry
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
open scoped Topology ENNReal BigOperators Classical


open QuadraticLocal.Advent Sycamore WilsonOlderFreshGraphAllStages WilsonOlderFreshGraphCommonSalary
open WilsonWindowBookPurchase WilsonLimitConstruction.FundedCompanySelection WilsonWindowUniversalSchool
variable {G:Gauge} {φ:ℕ→ℕ}


open WilsonOlderFreshGraphCommonHouse WilsonOlderFreshGraphCompiler WilsonOlderFreshGraphSlate

open WilsonNeutralPointCourse
open WilsonOlderFreshPointRegistry

def Ledger (R:Run G)(L:Primer.Families R.family)(a:hue G){d D:ℕ}(depth:d<D)(order:ℕ)(seed:ℕ→ℕ→ℝ)(δ:ℝ):Prop:=∃s:ℕ,∀m:ℕ,s ≤ m → ∀(N k:ℕ)(digit:∀j,Site (R.family.S.block j)),
    k ≤ R.alloy.B.a.clock.J m→1 ≤ Burn.horizon k→
    let σ:=fun j=>seed (Burn.horizon k) (R.alloy.B.a.clock.J j)
    ∃T:∀j, m≤j→j≤N→Letter (R.family.labels.level d)→Studio D→WilsonOlderFreshGraphSlate.Copy G d order (σ j),
      (∀j (lo:m≤j)(up:j≤N)(b:Letter (R.family.labels.level d))(f:Studio D),
        Filed R L a depth δ digit up b f (T j lo up b f)) ∧
      ∀j, m≤j→j<N→∀b:Letter (R.family.labels.level d),
        ∑v:Letter (R.family.labels.level d),∑l:Fin (order+1),|PowerSeries.coeff l.val (transfer R L a depth digit N j v b)|≤
          (R.family.path.levels.clock.hatBeta j)^δ

theorem original (R:Run G)(L:Primer.Families R.family)(a:hue G)(simple:G.Simple)(C:VowsR.LawScroll G φ)
    (split:MintClock.splits ≤ φ){U:ℕ→ℕ}(purchase:supply simple C split U R.kit)
    (strong:WilsonNeutralPointForecast.Filed R.kit)(weak:WilsonNeutralPointWeakForecast.Filed R.kit)
    (slow:∀j,((R.family.S.block j).val:ℝ)≤Real.log (RG16.Lambda R.family.path.levels j)):
    let M:=WilsonOlderFreshGraphAllStages.menu G
    let D:=roots M simple R.metals.p R.metals.K
    let Q:=rollTab M simple R.metals R.rolls
    ∃(B:Offices.Books D R.rolls Q φ)(F:Forecast D R.rolls Q φ B),
      Treehouse.VariableHouse R D Q C B R.family.path.levels.clock.kernel.penalty F (stages R.metals.p) ∧
      (∀(S:Query)(dmax:ℕ)(depth:S.letter.toll<dmax)(_:Loc G 1)(w:Letter (R.family.labels.level S.letter.toll))
        (δ:ℝ),0<δ→∀ᶠ i:ℕ in atTop,∀k:ℕ,k ≤ R.alloy.B.a.clock.J i→1 ≤ Burn.horizon k→
          WilsonOlderFreshGraphCommonSalary.Offered R L a S dmax i depth w
            (Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)) δ) ∧
      ∀(S:Query)(dmax:ℕ)(depth:S.letter.toll<dmax)(_:Loc G 1)(δ:ℝ),0<δ→
        Ledger R L a depth S.order (Agenda.seed D φ) δ:=by
  intro M D Q
  obtain ⟨B,F,house,avg,stage⟩:=WilsonOlderFreshPointSchool.original R L a simple C split purchase slow
  refine ⟨B,F,house,avg,?_⟩
  intro S dmax depth o δ pos
  have before:=WilsonNeutralPointWeakIncome.funded R L a depth o simple purchase.1.2 strong weak S.order
  have matrix:=(WilsonNeutralPointWeakIncome.original R L a depth o simple purchase.1.2 strong weak S.order).2
  obtain ⟨s,posted⟩:=eventually_atTop.mp ((stage S dmax depth o before δ pos).and
    (WilsonOlderFreshPointMatrixCash.original R L a depth simple S.order matrix pos))
  refine ⟨s,?_⟩
  intro m hm N k digit room rank σ
  have book(j:ℕ)(lo:m≤j)(up:j≤N)(b:Letter (R.family.labels.level S.letter.toll))(f:Studio dmax):
      ∃T:WilsonOlderFreshGraphSlate.Copy G S.letter.toll S.order (σ j),Filed R L a depth δ digit up b f T:=by
    let p:WilsonOlderFreshPointGauge.Ballot R j dmax:=(⟨N,up,digit⟩,f)
    obtain ⟨T,spent,read⟩:=(posted j (hm.trans lo)).1 k (room.trans (R.alloy.B.a.fits.mono lo)) rank b p
    exact ⟨T,spent,read,WilsonOlderFreshPointChart.original R L a depth j b p T read⟩
  choose t filed using book
  exact ⟨t,filed,fun j lo up b=>(posted j (hm.trans lo)).2 N up digit b⟩

end YM.Integration.WilsonOlderFreshPointHouseRegistry
end
