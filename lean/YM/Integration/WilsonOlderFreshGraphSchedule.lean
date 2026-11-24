import YM.Integration.WilsonOlderFreshGraphCommonHouse

/-! Choose a physical date once for the enrolled normalized field.
The actual next-date post, cutoff, period, test film and site may then be
quantified in that order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphSchedule
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


variable (R:Run G)(L:Primer.Families R.family)(a:hue G)

def Ready (D:AllOrder.Floe.Step.PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ:ℕ→ℕ)
    (S:Query)(dmax:ℕ)(depth:S.letter.toll<dmax)(w:Letter (R.family.labels.level S.letter.toll))
    {δ:ℝ}(hδ:0<δ)(i:ℕ):Prop:=
  (∀k:ℕ,k ≤ R.alloy.B.a.clock.J (i+1)→1 ≤ Burn.horizon k→
    Offered R L a S dmax (i+1) depth w (Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) (δ/2)) ∧
  WilsonMeasuredSemesterSubpower.onset R 1 (half_pos hδ) ≤ i

theorem on_run (simple:G.Simple) (C:VowsR.LawScroll G φ) (split:MintClock.splits ≤ φ)
    {U:ℕ→ℕ} (purchased:WilsonOlderFreshGraphCommonHouse.supply simple C split U R.kit):
    let M:=WilsonOlderFreshGraphAllStages.menu G
    let D:=roots M simple R.metals.p R.metals.K
    let Q:=rollTab M simple R.metals R.rolls
    ∃(B:Offices.Books D R.rolls Q φ)(F:Forecast D R.rolls Q φ B),
      Treehouse.VariableHouse R D Q C B R.family.path.levels.clock.kernel.penalty F (stages R.metals.p) ∧
      ∀(S:Query)(dmax:ℕ)(depth:S.letter.toll<dmax)(_:Loc G 1)(w:Letter (R.family.labels.level S.letter.toll))
        (δ:ℝ)(hδ:0<δ),∃b:ℕ,∀i:ℕ,b ≤ i→Ready R L a D φ S dmax depth w hδ i:=by
  intro M D Q
  obtain ⟨B,F,house,offered⟩:=WilsonOlderFreshGraphCommonHouse.original R L a simple C split purchased
  refine ⟨B,F,house,?_⟩
  intro S dmax depth o w δ hδ
  have after:=offered S dmax depth o w (δ/2) (half_pos hδ)
  have later:∀ᶠ i:ℕ in atTop, Ready R L a D φ S dmax depth w hδ i:=by
    filter_upwards [(tendsto_add_atTop_nat 1).eventually after,eventually_ge_atTop (WilsonMeasuredSemesterSubpower.onset R 1 (half_pos hδ))]
      with i printed live
    exact ⟨printed,live⟩
  exact eventually_atTop.mp later
end YM.Integration.WilsonOlderFreshGraphSchedule
end
