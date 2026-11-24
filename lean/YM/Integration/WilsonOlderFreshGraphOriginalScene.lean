import YM.Integration.WilsonOlderFreshGraphChildAverage
import YM.Integration.WilsonOlderSignedOneMarkScalarChain
/-! A single funded primitive and its actual filed family enter two
consecutive Wilson scene measurements. The physical scalar receives the
entire signed conditional residue with its original denominator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphOriginalScene
open OPE.Therm
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


private theorem finite {Y ι:Type}[Fintype ι][MeasurableSpace Y]{μ:Measure Y}(ρ:Y → ℝ)
    (a:ι → ℂ)(v:ι → Y → ℂ)(income:∀i,Integrable (fun U=>ρ U • v i U) μ):
    Integrable (fun U=>ρ U • (∑i,a i*v i U)) μ:=by
  apply (integrable_finsetSum Finset.univ (fun i _=>(income i).const_mul (a i))).congr
  filter_upwards [] with U
  simp only [Complex.real_smul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

include history scroll chamber warm top in
theorem original (cut:j+1<N)(T:Child → slate)(F:∀z:Child,lower z (T z))(high:ℕ)
    (space:Sycamore.Boot.need high school≤R.alloy.B.a.clock.J ((j+1)+1))
    (coarseSpace:Sycamore.Boot.need 0 school≤R.alloy.B.a.clock.J (j+1))
    (stamped:∀z:Child,∃H:upper z (T z),H.passport=passports z ∧ H.modelIndex=(T z).Roster ∧
      HEq H.model ((T z).rows (WilsonOlderFreshGraphPointWallet.point (place z)) A))
    (x:Wallet A)(h:Child → ℂ)(e:Config G lowerSide → ℂ)
    (signed:∀U,e U=actualAverage R.family (N:=N) (fun V=>∑z,h z*(sheet z (T z) x V)) U-
      ∑z,h z*(Spill.Foundry.uncut (F z).model gl x U).part u):
    (∫ U,e U ∂scene R.family.path N per (j+1)) =
      (∫ V,∑z,h z*(sheet z (T z) x V) ∂scene R.family.path N per ((j+1)+1))-
        (∫ U,∑z,h z*(Spill.Foundry.uncut (F z).model gl x U).part u ∂scene R.family.path N per (j+1)):=by
  let srcHi(z:Child)(U:Config G upperSide):=sheet z (T z) x U
  let srcLo(z:Child)(U:Config G lowerSide):=(Spill.Foundry.uncut (F z).model gl x U).part u
  let upperField(U:Config G upperSide):=∑z,h z*srcHi z U
  let lowerField(U:Config G lowerSide):=∑z,h z*srcLo z U
  have load:school.pieces≤Burn.horizon k+2:=by obtain ⟨_,_,_,v,_,_⟩:=school;exact v
  have fits:school.order≤Burn.horizon k+1:=by obtain ⟨_,_,_,_,v,_⟩:=school;exact v
  have packed:school.order+school.horizon≤Burn.horizon k+2:=by obtain ⟨_,_,_,_,_,v⟩:=school;exact v
  have fine(z:Child):Integrable (fun V=>(R.family.path.rep N per ((j+1)+1)).eval V • srcHi z V) (prior G upperSide):=by
    obtain ⟨H,pin,names,rows⟩:=stamped z
    have eq:=WilsonOlderFreshWordReversion.same H.model
      ((T z).rows (WilsonOlderFreshGraphPointWallet.point (place z)) A) pin names rows
    have paid:=WilsonOlderSignedOneMarkScalarChain.row R hk D Q₀ π Γ Ψ history books ahead A kernel grades
      school.order school.horizon school.pieces (floor.trans (Nat.le_succ j)) (birth z (T z)) H cut scroll chamber
      warm top fits load packed high space x ()
    simpa only [eq] using paid
  have coarse(z:Child):Integrable (fun U=>(R.family.path.rep N per (j+1)).eval U • srcLo z U) (prior G lowerSide):=
    WilsonOlderSignedOneMarkScalarChain.row R hk D Q₀ π Γ Ψ history books ahead A kernel grades
      school.order school.horizon school.pieces floor (down z (T z)) (F z) (Nat.lt_trans (Nat.lt_succ_self _) cut)
      scroll chamber warm top fits load packed 0 coarseSpace x ()
  have edge:=actualScene_step_error R.family R.makes cut (finite _ h srcLo coarse) (finite _ h srcHi fine)
  have flip:e=fun U=>-(lowerField U-actualAverage R.family (N:=N) upperField U):=by
    funext U
    calc
      e U=actualAverage R.family (N:=N) upperField U-lowerField U:=signed U
      _ = _:=by ring
  change _= (∫ V,upperField V ∂scene R.family.path N per ((j+1)+1))-
    (∫ U,lowerField U ∂scene R.family.path N per (j+1))
  rw [flip,integral_neg]
  change -(∫ U,lowerField U-actualAverage R.family (N:=N) upperField U ∂scene R.family.path N per (j+1))=_
  rw [edge]
  ring
end YM.Integration.WilsonOlderFreshGraphOriginalScene
end
