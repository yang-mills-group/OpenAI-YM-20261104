import YM.Integration.WilsonOlderFreshGraphChildDensity
import YM.Integration.WilsonOlderFreshGraphSlowPreimages
import YM.Integration.WilsonCenteredCaptureClock
/-! At a real coarse vertex sum the signed preimage comparisons on the one
receiving Wilson law. Each summand keeps its actual filed lower group word
and the same physical numerator used in its original push. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphOriginalChildSum
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G){m j N per k Q d:ℕ}
  (hk:Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q₀:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q₀ φ)
  (chamber:VowsR.Chamber scroll R.kit D Q₀ books) (floor:m ≤ j)

local notation "hi" => (floor.trans (Nat.le_succ j))

variable
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
  (school:Syl.School k)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J ((j+1)+1)) (R.alloy.B.a.clock.J (j+1)))
  (lesson:Lesson (N:=N) R hk D Q₀ π Γ hi)
  (cal:Oak.Calendar R hk D Q₀ π Γ Ψ hi (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q₀ φ books)
  (hospital:MintClock.Hospital D R.rolls Q₀ R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀"=> Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J ((j+1)+1))
variable (A:Unit→Set ℂ)
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
open WilsonOriginalReceivedChain


open Source
variable (base:Site (R.family.side (j+1) per))
local notation "ratio" => (R.family.path.levels.clock.op (j+1) per).ratio
local notation "Child" => Site ((R.family.path.levels.clock.op (j+1) per).ratio.count)
local notation "upperSide" => R.family.side ((j+1)+1) per
local notation "lowerSide" => R.family.side (j+1) per
local notation "place" => fun z:Child=>(ratio).assemble (base,z)
local notation "stock" => Stock.census Unit
local notation "u" => (Stock.census Unit).fire ()
local notation "kernel" => (fun _ : Unit => (⊥ : Submodule ℝ ℂ))
local notation "grades" => (fun _ : Unit => d)
local notation "slate" => WilsonOlderFreshGraphSlate.Copy G d Q σ₀
local notation "birth" => fun (z:Child) (T:slate) (t:Wallet A) (U:Config G upperSide) =>
  ((Ψ ((j+1)+1)).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut (T.rows (WilsonOlderFreshGraphPointWallet.point (place z)) A)
    (Coat.gStep (Ψ ((j+1)+1)).beta) t U)
local notation "down" => fun z (T:slate) (t:Wallet A)=>LocalComparison.actualPush R.family N per (j+1) (birth z T t)
local notation "lower" => fun z (T:slate)=>Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead
  A kernel grades school.order school.horizon school.pieces j floor (down z T)
local notation "origin" => fun z:Child=>((Earn.Passport.point (fun _:Unit=>place z)).coarser (ratio)).origin ()
local notation "rp" => Ψ (j+1)
local notation "F₁" => R.family.labels.level d
local notation "section₁" => R.family.localSection d
local notation "κ" => LocalComparison.forcedDivisor R.family (j+1)
local notation "gl" => Coat.gStep (Ψ (j+1)).beta

include history in
theorem original (cut:j+1<N) (T:Child → slate)(F:∀z:Child,lower z (T z))
    (t:Wallet A)(h:Child → ℂ)(lim:Child → ℝ)
    (bills:∀z:Child,∃(E:Coefficient F₁ lowerSide)(b:ℝ),
      E.Format (origin z) R.family.params rp ∧ E.remBound (origin z) rp κ b ∧
      (∀U,E.density (origin z) section₁ rp U=(down z (T z) t U).part u-
        ((rp).eval U:ℂ)*(Spill.Foundry.uncut (F z).model gl t U).part u) ∧ b+(F₁).coeffSize E.x ≤ lim z):
    ∃(E:Coefficient F₁ lowerSide)(b:ℝ), E.Format base R.family.params rp ∧ E.remBound base rp κ b ∧
      (∀U,E.density base section₁ rp U=(∑z,h z*(down z (T z) t U).part u)-
        ((rp).eval U:ℂ)*(∑z,h z*(Spill.Foundry.uncut (F z).model gl t U).part u)) ∧
      b+(F₁).coeffSize E.x ≤ ∑z,‖h z‖*lim z:=by
  have here(z:Child):origin z=base:=(ratio).assemble_parent _
  simp only [here] at bills
  choose E b format bound row price using bills
  have lawful:=(history.1.walk (j+1) (floor.trans (Nat.le_succ j)) cut.le).truep.valid
  have κpos:0<κ:=Real.sqrt_pos.mpr (Push.Local.allowance_pos R.family.path.levels.clock (j+1))
  let upper(x:Child)(U:Config G lowerSide):=(down x (T x) t U).part u
  let filed(x:Child)(U:Config G lowerSide):=(Spill.Foundry.uncut (F x).model gl t U).part u
  obtain ⟨fmt,rem,_,primary,density⟩:=WilsonOlderFreshGraphChildDensity.represented lawful κpos h E b
    format bound upper filed row
  refine ⟨WilsonOlderFreshGraphChildDensity.collected h E,∑z,‖h z‖*b z,fmt,rem,density,?_⟩
  calc
    _ ≤ (∑z,‖h z‖*b z)+∑z,‖h z‖*(F₁).coeffSize (E z).x:=add_le_add_right primary _
    _ = ∑z,‖h z‖*(b z+(F₁).coeffSize (E z).x):=by simp only [mul_add,Finset.sum_add_distrib]
    _ ≤ _:=Finset.sum_le_sum fun z _=>mul_le_mul_of_nonneg_left (price z) (norm_nonneg _)
end YM.Integration.WilsonOlderFreshGraphOriginalChildSum
end
