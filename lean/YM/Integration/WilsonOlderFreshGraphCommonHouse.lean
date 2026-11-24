import YM.Integration.WilsonOlderFreshGraphPhysicalSalary
import YM.Integration.WilsonWindowUniversalSchool

/-! The variable physical school and the normalized-column salaries have
exactly the same run, roots, roll table, and books, chosen once. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphCommonHouse
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

def course (C:VowsR.LawScroll G φ) (split:MintClock.splits ≤ φ):VowsR.LawScroll G φ:=
  Tracks.vine (WilsonWindowUniversalSchool.flow C) split

def supply (simple:G.Simple) (C:VowsR.LawScroll G φ)(split:MintClock.splits ≤ φ)(U:ℕ→ℕ):Prediction G:=
  Together (Together (@WilsonOlderFreshGraphSchool.grant G φ (WilsonOlderFreshGraphAllStages.menu G) simple
    (WilsonOlderFreshGraphMatrixPrice.jointLaw (course C split))) (@WilsonWindowFormalPurchase.Canonical G U))
    (@WilsonWindowVacuumAdmission.Ready G)

theorem prepaid (simple:G.Simple) (C:VowsR.LawScroll G φ) (split:MintClock.splits ≤ φ) (U:ℕ→ℕ)
    (paid:∀(s:Sheet G)(q:MapPrices),Permitted C s (ThroughLaunch.raging s q)):
    AllPrices (@supply G φ simple C split U):=fun s q=>joint
      (WilsonOlderFreshGraphAllStages.prepared simple (course C split) U
        (fun s q=>WilsonWindowCourseLaws.physical_course split (paid s q)) s q)
      (WilsonWindowVacuumAdmission.prepaid simple s _)

theorem original (R:Run G) (L:Primer.Families R.family)(a:hue G)(simple:G.Simple)
    (C:VowsR.LawScroll G φ) (split:MintClock.splits ≤ φ) {U:ℕ→ℕ} (purchased:supply simple C split U R.kit):
    let M:=WilsonOlderFreshGraphAllStages.menu G
    let D:=roots M simple R.metals.p R.metals.K
    let Q:=rollTab M simple R.metals R.rolls
    ∃(B:Offices.Books D R.rolls Q φ)(F:Forecast D R.rolls Q φ B),
      Treehouse.VariableHouse R D Q C B R.family.path.levels.clock.kernel.penalty F (stages R.metals.p) ∧
      ∀(S:Query)(dmax:ℕ)(depth:S.letter.toll<dmax)(_:Loc G 1)(w:Letter (R.family.labels.level S.letter.toll))
        (δ:ℝ),0<δ→∀ᶠ i:ℕ in atTop,∀k:ℕ,k ≤ R.alloy.B.a.clock.J i→1 ≤ Burn.horizon k→
          Offered R L a S dmax i depth w (Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)) δ:=by
  intro M D Q
  obtain ⟨⟨B,held⟩,filed⟩:=WilsonOlderFreshGraphCommonSalary.original R L a simple (course C split) purchased.1
  obtain ⟨F,house⟩:=WilsonWindowUniversalSchool.house simple R D Q C B split held purchased.2
  exact ⟨B,F,house,filed⟩
end YM.Integration.WilsonOlderFreshGraphCommonHouse
end
