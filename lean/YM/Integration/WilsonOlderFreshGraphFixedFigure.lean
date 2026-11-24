import YM.Integration.WilsonOlderFreshGraphReceivingFigure
import YM.Integration.WilsonOlderFreshGraphInvoiceOrder
/-! Report the fixed source horizon on the original receiving register, including its actual curvature strip. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphFixedFigure
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
  (hk:Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q₀:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q₀ φ)
  (floor:m ≤ j)

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
local notation "massF"=>‖Annex.compress dmax f‖


variable (base:Site (R.family.side (j+1) per))
local notation "child" => Site (R.family.path.levels.S.block (j+1))
local notation "place" => fun z:child=>(R.family.path.levels.clock.op (j+1) per).ratio.assemble (base,z)
local notation "testAt" => fun z:child=>Dawn.throughW z dmax (Elm.growL R.family.path.levels (j+1)) f
local notation "salary" => fun z:child=>1+‖Annex.compress dmax (testAt z)‖
local notation "slate" => WilsonOlderFreshGraphSlate.Copy G query.letter.toll query.order σ₀
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N per j
variable (p:ℕ) {ε:ℝ} (ep:0 < ε)
local notation "q₁" => (p+2+2)
private theorem divide_pos {ε:ℝ} (ep:0 < ε) : 0 < ε/16 := div_pos ep (by norm_num)
local notation "ep₀" => divide_pos ep

private theorem ready_order {q J:ℕ} (h:2*(q+4+1)+8 ≤ J) : 2*q+8 ≤ J := by omega
private theorem ready_age {q k:ℕ} (h:q+4+4 ≤ 3*k+2) : q+3 ≤ 3*k+2 := by omega

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
local notation "material" => fun (z:child)(T:slate)(t:Wallet A)(U:Config G upperSide)=>
  (Spill.Foundry.uncut (T.rows (WilsonOlderFreshGraphPointWallet.point (place z)) A) gu t U).part u
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle QuadraticLocal.Earn Primitives.TwoWave
open WilsonNeutralRenderedColumn WilsonOriginalPrimerFiledPages

local notation "account" H:max => Oak.figureReal R hk D Q₀ π Γ books hi (H).op (H).lesson ahead school.order school.horizon
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1))
local notation "expo" => (Ψ (j+1)).p.supportExponent+2
local notation "height" => school.order+school.horizon+1


local notation "full" => (2:ℝ)^height * budgetR R i₁

include history in
theorem original (simple:G.Simple)(cut:i₁<N)(late:WilsonOlderFreshGraphReceivingFigure.first R simple ≤ i₁)
    (d:ℕ)(licensed:d ≤ school.horizon)(z:child)(T:slate)(H:upper z T):
    (account H).limitC = σ/4 ∧
    Invoice.Supports (Ψ i₁).p (2*(account H).mist) expo (Coat.gStep (Ψ i₁).beta) σ (σ/4) ∧
    expo*((Ψ i₁).p.B:ℝ)⁻¹ ≤ σ/2 ∧
    Real.exp ((σ/4)/2) ≤ 16*full ∧
    Invoice.price (Ψ i₁).p (2*(account H).mist) (school.order+d+1) school.pieces expo (σ/4) G
      ≤ 256*full^3:=by
  obtain ⟨paid,total⟩:= WilsonOlderFreshGraphReceivingFigure.original R query hk D Q₀ π Γ Ψ history
    books floor school ahead A base simple cut late z T H
  have strip:(account H).limitC=σ/4:=by rfl
  rw [strip] at paid total
  have intact:=paid
  obtain ⟨_,_,room,_,_,ax,good,spare⟩:=paid
  have rank:school.order+d+1≤height:=by omega
  refine ⟨strip,intact,?_,?_,?_⟩
  · linarith only [spare]
  · exact (WilsonOlderFreshGraphInvoiceOrder.escape G (Ψ i₁).p room ax good height school.pieces).trans
      (mul_le_mul_of_nonneg_left total (by norm_num))
  · have starts:=WilsonOlderFreshGraphInvoiceOrder.escape G (Ψ i₁).p room ax good height school.pieces
    have gross:0≤Invoice.price (Ψ i₁).p (2*(account H).mist) height school.pieces expo (σ/4) G:=by
      linarith [Real.exp_pos ((σ/4)/2)]
    exact (WilsonOlderFreshGraphInvoiceOrder.controlled G (Ψ i₁).p room ax good school.pieces rank).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ gross total _) (by norm_num))

end YM.Integration.WilsonOlderFreshGraphFixedFigure
end
