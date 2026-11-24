import YM.Integration.WilsonMeasuredIssuedChildCash
/-! A literal one-child Wilson row pays its cell factor once on the same original stamped posts. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedPointChildCash
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

variable (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)

include history in
theorem original (cut:i₁<N)(pass:Pass D Q₀ R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q₀ R.kit.target φ books ahead R.alloy.delay)
    (later:WilsonMeasuredIssuedChildCash.first R query simple slow ≤ i₁) (shelved:school.horizon≤R.alloy.B.a.clock.J i₁)
    (load:school.pieces≤Burn.horizon k+2) (T:child→slate)
    (H:∀z,upper z (T z)) (F:∀z,lower z (T z)) (amp:child→ℝ)
    (bought:∀z,0<amp z ∧ (amp z)⁻¹≤2*βhat*(salary z))
    (earned:∀z,∃h C:ℝ,1≤h ∧ C≤budgetR R i₁ ∧
      (∀v,(F z).w v=amp z/((Oak.expenseReal R hk D Q₀ π Γ books hi (H z).op
        (H z).lesson ahead school.order school.horizon)^6*h)) ∧ (F z).cost=h⁻¹*C):
    ∀ pin:child,(∑z:child,|if z=pin then ((blockSide).val:ℝ)^4*Kemp.aven blockSide query.letter.toll else 0| *
      ((Poly.toll (F z).w u)⁻¹*(F z).cost)) ≤32*(R.alloy.B.a.clock.hatBeta i₁)^4*(1+massF) := by
  classical
  intro pin
  have bounds:=max_le_iff.mp later
  have narrow:=max_le_iff.mp bounds.2
  have width:((blockSide).val:ℝ)^query.letter.toll≤βhat:=by
    have bought' := (eventually_atTop.mp (WilsonOlderFreshGraphSlowPreimages.block R simple slow query.letter.toll
      (show 0<(1:ℝ) by norm_num))).choose_spec i₁ narrow.1
    have levels:R.family.path.levels=R.alloy.B.a:=rfl
    rw [levels]
    simpa only [Real.rpow_one] using bought'
  have grow:βhat≤2*R.alloy.B.a.clock.hatBeta i₁:=
    (eventually_atTop.mp (RG01.Physical.nextHat simple R.family.path.levels)).choose_spec i₁ narrow.2
  have B:0≤βhat:=(zero_lt_one.trans (R.alloy.B.a.fits.delayed (i₁+1))).le
  have rateAgree:|Kemp.aven blockSide query.letter.toll|=rate:=by
    rw [Kemp.aven,abs_of_nonneg (by positivity),Lattice.site_card,Nat.cast_pow,div_eq_mul_inv]
  have each (z:child) := WilsonEmittedChildFinance.original (R:=R) (hk:=hk) (D:=D) (Q:=Q₀)
    (π:=π) (Γ:=Γ) (Ψ:=Ψ) (course:=history) (books:=books) (ahead:=ahead) (school:=school)
    (floor:=floor) (actors:=A) (inputRank:=query.letter.toll)
    (model:=((T z).rows (WilsonOlderFreshGraphPointWallet.point (place z)) A)) (cut:=cut) (pass:=pass)
    (H z) (F z) bounds.1 hospital shelved load (bought z).1
    (show 0 ≤ salary z by dsimp; positivity) (bought z).2 (earned z)
  have testCap:=WilsonOlderFreshGraphChildFare.compressed (R.family.path.levels.S.block_odd i₁)
    (Elm.growL R.family.path.levels i₁) pin f
  have one:(Poly.toll (F pin).w u)⁻¹*(F pin).cost ≤ 2*βhat^3*(1+massF):=
    (each pin).trans (mul_le_mul_of_nonneg_left (add_le_add_right testCap 1) (by positivity))
  have sidepos:0 < ((blockSide).val:ℝ):=by exact_mod_cast (blockSide).pos
  have compensated:((blockSide).val:ℝ)^4*rate=((blockSide).val:ℝ)^query.letter.toll:=by field_simp
  rw [Finset.sum_eq_single pin (fun q _ h=>by simp [h]) (by simp),if_pos rfl,
    abs_mul,abs_of_nonneg (pow_nonneg sidepos.le _),rateAgree,compensated]
  calc
    _ ≤ ((blockSide).val:ℝ)^query.letter.toll*(2*βhat^3*(1+massF)):=mul_le_mul_of_nonneg_left one (by positivity)
    _ ≤ βhat*(2*βhat^3*(1+massF)):=mul_le_mul_of_nonneg_right width (by positivity)
    _ = 2*βhat^4*(1+massF):=by ring
    _ ≤ 2*(2*R.alloy.B.a.clock.hatBeta i₁)^4*(1+massF):=by gcongr
    _ = _:=by ring

end YM.Integration.WilsonEmittedPointChildCash
end
