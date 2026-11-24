import YM.Integration.WilsonOlderFreshGraphConditionalSum
import YM.Integration.WilsonOlderFreshGraphFiledPreimages
/-! For the real stamped physical templates, the sum of all conditional
numerators over actual fine preimages is one hearing against the entire
original Wilson intake. Its source and unmarked denominator are measured
on the same course. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphChildAverage
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


local notation "passports" => fun z:Child=>Earn.Passport.point (fun _:Unit=>place z)
local notation "upper" => fun z (T:slate)=>Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead
  A kernel grades school.order school.horizon school.pieces (j+1) (floor.trans (Nat.le_succ j)) (birth z T)


open MeasureTheory
local notation "gu" => Coat.gStep (Ψ ((j+1)+1)).beta
local notation "sheet" => fun (z:Child)(T:slate)(x:Wallet A)(U:Config G upperSide)=>
  (Spill.Foundry.uncut (T.rows (WilsonOlderFreshGraphPointWallet.point (place z)) A) gu x U).part u

include history scroll chamber warm top in
theorem original (cut:j+1<N)(T:Child → slate)(high:ℕ)
    (space:Sycamore.Boot.need high school≤R.alloy.B.a.clock.J ((j+1)+1))
    (stamped:∀z:Child,∃H:upper z (T z),H.passport=passports z ∧ H.modelIndex=(T z).Roster ∧
      HEq H.model ((T z).rows (WilsonOlderFreshGraphPointWallet.point (place z)) A))
    (x:Wallet A)(h:Child → ℂ)(W:Config G lowerSide):
    ((rp).eval W:ℂ)*actualAverage R.family (N:=N) (fun U=>∑z,h z*(sheet z (T z) x U)) W =
      ∑z,h z*(down z (T z) x W).part u:=by
  have up:(Ψ ((j+1)+1)).eval=(R.family.path.rep N per ((j+1)+1)).eval:=
    (history.1.walk ((j+1)+1) ((floor.trans (Nat.le_succ j)).trans (Nat.le_succ _)) cut).view
  have dn:(rp).eval=(R.family.path.rep N per (j+1)).eval:=
    (history.1.walk (j+1) (floor.trans (Nat.le_succ j)) cut.le).view
  let word(z:Child)(U:Config G upperSide):=Spill.Foundry.uncut
    ((T z).rows (WilsonOlderFreshGraphPointWallet.point (place z)) A) gu x U
  let panel(z:Child)(U:Config G upperSide):=Poly.pass (word z U)
  have load:school.pieces≤Burn.horizon k+2:=by obtain ⟨_,_,_,v,_,_⟩:=school;exact v
  have fits:school.order≤Burn.horizon k+1:=by obtain ⟨_,_,_,_,v,_⟩:=school;exact v
  have packed:school.order+school.horizon≤Burn.horizon k+2:=by obtain ⟨_,_,_,_,_,v⟩:=school;exact v
  have income(z:Child):Integrable (fun U=>((R.family.path.rep N per ((j+1)+1)).eval U:ℂ) • panel z U) (prior G upperSide):=by
    obtain ⟨H,pin,names,rows⟩:=stamped z
    have eq:=WilsonOlderFreshWordReversion.same H.model
      ((T z).rows (WilsonOlderFreshGraphPointWallet.point (place z)) A) pin names rows
    have live:=WilsonOlderSignedOneMarkAdmitted.original R hk D Q₀ π Γ Ψ history books ahead A kernel
      grades school.order school.horizon school.pieces (floor.trans (Nat.le_succ j)) (birth z (T z)) H cut scroll
      chamber warm top fits load packed high space x
    simpa only [eq,←up] using live
  have read(z:Child)(U:Config G upperSide):(panel z U).part u=(word z U).part u:=
    MergeProof.Accent.whisper _ _ (WilsonOlderFreshWordReversion.quiet
      ((T z).rows (WilsonOlderFreshGraphPointWallet.point (place z)) A) x gu U) ()
  have all:=WilsonOlderFreshGraphConditionalSum.marked R.family R.makes cut u h panel income W
  rw [←up,←dn] at all
  simpa only [read] using all
end YM.Integration.WilsonOlderFreshGraphChildAverage
end
