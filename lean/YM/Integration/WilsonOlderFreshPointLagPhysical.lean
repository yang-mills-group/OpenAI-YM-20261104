import YM.Integration.WilsonOlderFreshPointGradeReturn
import YM.Integration.WilsonOlderFreshPointLagPower
import YM.Integration.WilsonMeasuredPointStride
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointLagPhysical
open OPE.Therm
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G){m j N per k:ℕ} (query:WilsonOlderFreshGraphAllStages.Query)
  (hk:Burn.horizon k+2   ≤   R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q₀:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q₀ φ)
  (floor:m  ≤  j)

local notation "hi" => (floor.trans (Nat.le_succ j))
local notation "i₁" => (j+1)
variable
  (top:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
  (school:Syl.School k)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J ((j+1)+1)) (R.alloy.B.a.clock.J (j+1)))
  (lesson:Lesson (N:=N) R hk D Q₀ π Γ (floor.trans (Nat.le_succ j)))
  (cal:Oak.Calendar R hk D Q₀ π Γ Ψ (floor.trans (Nat.le_succ j)) (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q₀ φ books)
  {ZΘ:ℝ} {profile:PhysicalNext.ThroughLaunch.Orders}
  (house:QuadraticLocal.Advent.Sycamore.Treehouse.VariableHouse R D Q₀ scroll books ZΘ ahead profile)
local notation "σ₀"=> Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i₁+1))
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
open WilsonOriginalReceivedChain WilsonMeasuredRankedResidual Pert.Asymptotics

local notation "families" => (fun u:ℕ=>Flat.routes (R.family.path.levels.clock.op u 0).patch)
variable {dmax:ℕ} (a:hue G) (depth:query.letter.toll<dmax)
    (w:Letter (R.family.labels.level query.letter.toll)) (f:Studio dmax)
local notation "Ω₀"=>Oak.expenseReal R hk D Q₀ π Γ books hi op lesson ahead school.order school.horizon

local notation "βhat"=>R.alloy.B.a.clock.hatBeta (i₁+1)
local notation "massF"=>‖f‖


variable (base:Site (R.family.side (j+1) per))
local notation "child" => Site (R.family.path.levels.S.block (j+1))
local notation "place" => fun z:child=>(R.family.path.levels.clock.op (j+1) per).ratio.assemble (base,z)
local notation "testAt" => fun z:child=>Dawn.throughW z dmax (Elm.growL R.family.path.levels (j+1)) f
local notation "salary" => fun z:child=>1+‖testAt z‖
local notation "slate" => WilsonOlderFreshGraphSlate.Copy G query.letter.toll query.order σ₀
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N per j
variable (p:ℕ) {ε:ℝ} (ep:0 < ε)
local notation "q₁" => (p+2+2)
private theorem divide_pos {ε:ℝ} (ep:0 < ε) : 0 < ε/16 := div_pos ep (by norm_num)
local notation "ep₀" => divide_pos ep

private theorem ready_order {q J:ℕ} (h:2*(q+4+1)+8  ≤  J) : 2*q+8  ≤  J := by omega
private theorem ready_age {q k:ℕ} (h:q+4+4  ≤  3*k+2) : q+3  ≤  3*k+2 := by omega

local notation "upperSide" => R.family.side ((j+1)+1) per
local notation "lowerSide" => R.family.side (j+1) per
local notation "stock" => Stock.census Unit
local notation "u" => (Stock.census Unit).fire ()
local notation "kernel" => (fun _ : Unit => (⊥ : Submodule ℝ ℂ))
local notation "grades" => (fun _ : Unit => query.letter.toll)
local notation "birth" => fun (z:child) (T:slate) (t:Wallet A) (U:Config G upperSide) =>
  ((Ψ ((j+1)+1)).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut (T.rows (WilsonOlderFreshGraphPointWallet.point (place z)) A)
    (Coat.gStep (Ψ ((j+1)+1)).beta) t U)
local notation "down" => fun z (T:slate) (t:Wallet A)=>LocalComparison.actualPush R.family N per (j+1) (birth z T t)
local notation "lower" => fun z (T:slate)=>Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead
  A kernel grades school.order school.horizon school.pieces j floor (down z T)
local notation "origin" => fun z:child=>((Earn.Passport.point (fun _:Unit=>place z)).coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin ()
local notation "rp" => Ψ (j+1)
local notation "F₁" => R.family.labels.level query.letter.toll
local notation "section₁" => R.family.localSection query.letter.toll
local notation "κ" => LocalComparison.forcedDivisor R.family (j+1)
local notation "gl" => Coat.gStep (Ψ (j+1)).beta


local notation "passports" => fun z:child=>Earn.Passport.point (fun _:Unit=>place z)
local notation "upper" => fun z (T:slate)=>Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead
  A kernel grades school.order school.horizon school.pieces (j+1) (floor.trans (Nat.le_succ j)) (birth z T)



local notation "blockSide" => R.family.path.levels.S.block (j+1)
local notation "rate" => (((blockSide).val:ℝ)^query.letter.toll/((blockSide).val:ℝ)^4)

local notation "gu" => Coat.gStep (Ψ ((j+1)+1)).beta
local notation "material" => fun (z:child) (T:slate) (t:Wallet A) (U:Config G upperSide)=>
  (Spill.Foundry.uncut (T.rows (WilsonOlderFreshGraphPointWallet.point (place z)) A) gu t U).part u
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle QuadraticLocal.Earn Primitives.TwoWave
open WilsonNeutralRenderedColumn WilsonOriginalPrimerFiledPages

open WilsonMeasuredTransitionCatalogue
open WilsonMeasuredOriginalCatalogueUnion WilsonEmittedFiledGerm
open QuadraticLocal.Earn
local notation "letter" => Letter F₁
local notation "S₀" => (WilsonOlderFreshGraphPointWallet.point base)
local notation "unitMark" => (WilsonNeutralRenderedColumn.submitted S₀)
variable (digit:∀i,Site (R.family.S.block i))
local notation "pin" => digit i₁
local notation "g₁" => (((blockSide).val:ℝ)^query.letter.toll)
local notation "coef" => fun(v:letter)(ν:ℕ)=>PowerSeries.coeff ν
  (WilsonNeutralPointCourse.transfer R families a depth digit N i₁ v w)
local notation "prior" T₀:max => fun v:letter=>(T₀ v).rows S₀ A
local notation "pole₁" => Launch.index stock grades u + 1


local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i₁)
open WilsonMeasuredJointCensusCash
variable (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit)
open WilsonEmittedDictionary Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open WilsonLimitConstruction.FundedDictionaryPatchPrices
open WilsonEmittedOriginalReturn Push.AbsoluteSums
local notation "target" d:max q:max=>2*4+(d+1)+1+(q+3)
local notation "account" H:max => Oak.figureReal R hk D Q₀ π Γ books hi (H).op (H).lesson ahead school.order school.horizon


open Extra.Histories
local notation "gain" ℓ:max => ((gl^ℓ*g₁):ℝ)
include history in
theorem original (cut:i₁<N)(late:WilsonOlderFreshPointLagPower.start R simple slow query.letter.toll ≤ j)
    (T:slate)(F:lower pin T)(t:Wallet A)(E:Coefficient F₁ lowerSide){b ε n:ℝ}(q ℓ:ℕ)
    (ep:0≤ε)(np:0≤n)(fmt:E.Format base R.family.params rp)(hard:E.remBound base rp κ b)
    (actual:∀U,E.density base section₁ rp U=(down pin T t U).part u-((rp).eval U:ℂ)*(Spill.Foundry.uncut F.model gl t U).part u)
    (earned:b+(F₁).coeffSize E.x≤(ε/8)*g₀^(q+2)*n):
    let Z:=Extra.Histories.stretch (↑(gain ℓ):ℂ) E
    Z.Format base R.family.params rp ∧ Z.remBound base rp κ ((gain ℓ)*b) ∧
    (∀U,Z.density base section₁ rp U=(↑(gain ℓ):ℂ)*((down pin T t U).part u-
      ((rp).eval U:ℂ)*(Spill.Foundry.uncut F.model gl t U).part u)) ∧
    (gain ℓ)*b+(F₁).coeffSize Z.x≤ε*g₀^q*n:=by
  let Z:=Extra.Histories.stretch (↑(gain ℓ):ℂ) E
  have price:=WilsonOlderFreshPointLagPower.native (N:=N) (per:=per) R simple slow query.letter.toll ℓ cut late
  have actualg:gl=Pert.Asymptotics.regulatorRun R.family N per i₁:=by
    rw [(history.1.walk i₁ hi cut.le).beta];rfl
  dsimp only at price
  rw [←actualg] at price
  have norm:‖(↑(gain ℓ):ℂ)‖=gain ℓ:=by rw [Complex.norm_real,Real.norm_of_nonneg price.1]
  refine ⟨Extra.Histories.stretch_format _ fmt,?_,?_,?_⟩
  · exact (congrArg (fun v:ℝ=>Z.remBound base rp κ (v*b)) norm).mp (Extra.Histories.stretch_rem _ hard)
  · intro U
    calc
      _ = (↑(gain ℓ):ℂ)*E.density base section₁ rp U:=Extra.Histories.stretch_density ..
      _ = _:=congrArg _ (actual U)
  · change (gain ℓ)*b+(F₁).coeffSize ((↑(gain ℓ):ℂ) • E.x)≤_
    rw [Extra.Histories.Size.smul,norm,←mul_add]
    exact WilsonMeasuredPointStride.rescaled q price.1 ep price.2.1.le np price.2.2 earned

end YM.Integration.WilsonOlderFreshPointLagPhysical
