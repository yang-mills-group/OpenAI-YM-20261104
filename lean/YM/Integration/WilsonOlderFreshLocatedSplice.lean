import YM.Integration.WilsonNeutralReportCommonTail
import YM.Integration.WilsonOlderFreshLocatedIssued
import YM.Integration.WilsonOlderFreshLocatedRoster
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshLocatedSplice
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
variable {G:Gauge} {φ:ℕ → ℕ}


open WilsonOlderFreshGraphCommonHouse WilsonOlderFreshGraphCompiler WilsonOlderFreshGraphSlate

open WilsonNeutralPointCourse
open WilsonOlderFreshPointRegistry


open QuadraticLocal.Affinity WilsonOlderFreshLocatedRoster WilsonOlderFreshLocatedBook
variable {G:Gauge}(R:Run G)(L:Primer.Families R.family)(a:hue G){d D Q m N s:ℕ}(depth:d<D)
  {first second:∀i,Site (R.family.S.block i)}
  {σ:ℕ → ℝ}
local notation "axes" => Letter (R.family.labels.level d)

theorem admitted {j:ℕ}(up:j ≤ N)(joined:∀i,j ≤ i → i<N → first i=second i)
    (b:axes)(f:Studio D)(T:WilsonOlderFreshGraphSlate.Copy G d Q (σ j))
    (old:Filed R L a depth (1/4) first up b f T):
    Filed R L a depth (1/4) second up b f T:=by
  have upper:=WilsonNeutralReportCommonTail.field R L a depth up joined b f
  have charts:=WilsonNeutralReportCommonTail.chart R L a depth up joined b f
  refine ⟨old.1,?_,?_⟩
  · intro z n A t
    unfold WilsonOlderFreshPointGauge.panel
    rw [←upper]
    exact old.2.1 z n A t
  · rw [←charts]
    exact old.2.2

abbrev Table (σ:ℕ → ℝ):=∀i:ℕ,m ≤ i → i ≤ N → axes → Studio D → WilsonOlderFreshGraphSlate.Copy G d Q (σ i)
def patch (s:ℕ)(upper lower:Table (m:=m) (N:=N) (d:=d) (D:=D) (Q:=Q) R σ):
    Table (m:=m) (N:=N) (d:=d) (D:=D) (Q:=Q) R σ :=
  fun i lo live=>if s ≤ i then upper i lo live else lower i lo live

theorem original (upper lower:Table (m:=m) (N:=N) (d:=d) (D:=D) (Q:=Q) R σ)
    (joined:∀i,s ≤ i → i<N → first i=second i)
    (b₀:Booked R L a depth Q σ m N first upper)(b₁:Booked R L a depth Q σ m N second lower):
    Booked R L a depth Q σ m N second (patch R s upper lower):=by
  refine ⟨?_,b₁.2⟩
  intro i lo up b f
  by_cases reached:s ≤ i
  · rw [patch,if_pos reached]
    exact admitted R L a depth up (fun j start high=>joined j (reached.trans start) high) b f _ (b₀.1 i lo up b f)
  · rw [patch,if_neg reached]
    exact b₁.1 i lo up b f

theorem held (upper lower:Table (m:=m) (N:=N) (d:=d) (D:=D) (Q:=Q) R σ)
    {per i:ℕ}(lo:m ≤ i)(up:i ≤ N)(reached:s ≤ i)
    (sites₁ sites₂:∀j,Site (R.family.side j per))(p₁ p₂:ℕ → Studio D)(A:Unit → Set ℂ)(x:Wallet A)(g:ℕ → ℝ)
    (address:sites₁ i=sites₂ i)(film:p₁ i=p₂ i)(b:axes)(U:Config G (R.family.side i per)):
    fixed R σ (patch R s upper lower) sites₂ p₂ A x g i b U=fixed R σ upper sites₁ p₁ A x g i b U:=by
  rw [at_date R σ _ sites₂ p₂ A x g lo up,at_date R σ upper sites₁ p₁ A x g lo up]
  rw [patch,if_pos reached,address,film]

end YM.Integration.WilsonOlderFreshLocatedSplice
end
