import YM.Integration.WilsonOlderFreshGraphFundedHearing
import YM.Integration.WilsonOlderFreshGraphOriginalScene
import YM.Integration.WilsonOlderFreshGraphChildAverage
/-! The finite collection commissioned by the before-regulator school in a single
original Wilson expectation. The conditional and unconditional comparisons use
the identical appointed upper and signed lower source at each child. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphFundedScene
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

variable {dmax:ℕ} (L:Primer.Families R.family) (a:hue G) (depth:query.letter.toll<dmax)
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
/-- The lower scene's original integrability appointment precedes either regulator. -/
theorem lower_appointment (R:Run G) (school:Syl.School k) :
    ∃n:ℕ,∀j≥n,Sycamore.Boot.need 0 school ≤ R.alloy.B.a.clock.J (j+1):=by
  exact eventually_atTop.mp ((R.alloy.B.a.fits.deep.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop _)

noncomputable def opening (R:Run G)(school:Syl.School k):ℕ:=(lower_appointment R school).choose

include history scroll top cal house in
theorem original (simple:G.Simple) (cut:i₁<N) (cap:∀t,‖value A t‖≤1)
    {τ:ℝ} (pos:0<τ) (bounded:τ≤1)
    (schedule:WilsonOlderFreshGraphSchedule.Ready R L a D φ query dmax depth w (show 0<(1:ℝ) by norm_num) (j+1))
    (lateScene:opening R school ≤ j) (kpos:1≤k)
    (seats:1≤op.count) (shape:op.count=school.pieces) (phase:school.order+1 ≤ op.stage)
    (enrolled:query.order ≤ school.order) (within:query.letter.toll ≤ school.horizon) (budget:school.order+query.letter.toll ≤ Burn.horizon k+2)
    (high:ℕ) (space:Sycamore.Boot.need high school ≤ R.alloy.B.a.clock.J (i₁+1))
    (path:PlanV.Path D R.alloy Q₀ (Burn.horizon k) N m π Γ)
    (month:Scholar.Month R.rolls D Q₀ R.alloy.delay)
    (narrow:school.horizon≤R.alloy.B.a.clock.J i₁)
    (M₀:WilsonMeasuredRankedMenu.Menu R query.letter.toll) (office:M₀.onset ≤ i₁) (way : WayStation R.kit) 
    (pace:WilsonWindowReportingPace.Slow R.kit)
    (prepared : WilsonReportLampForecast.Ready R.family.path.levels)
    (fixed : (R.family.path.levels.budget i₁).supportExponent ≤ 100)
    (date : R.t query.letter.toll ≤ i₁) (late : WilsonCenteredCaptureClock.first R simple ≤ i₁)
    (grossDate : WilsonReceivedSourceGross.opening R simple ≤ i₁)
    (fareDate : WilsonOlderSignedOneMarkPhysicalFare.opening R simple pace.2 prepared ≤ i₁)
    (ready : q₁+1+6 ≤ R.alloy.B.a.clock.J i₁) (deep : 2*(q₁+4+1)+8 ≤ school.order)
    (aged : q₁+4+4 ≤ 3*k+2) 
    (opened : WilsonFirstReceivedEarnedFee.opening R simple school.pieces (q₁+4) school.order k deep aged
      (tolerance_pos R query.letter.toll q₁ (WilsonMeasuredRankedMenu.fee_positive R query.letter.toll M₀ ep₀)) ≤ i₁)
    (recalled : WilsonCoherentMayerMutationIntake.firstDate R simple school.order (show (0:ℝ)<1 by norm_num)
      le_rfl (tolerance_pos R query.letter.toll q₁ (WilsonMeasuredRankedMenu.fee_positive R query.letter.toll M₀ ep₀)) ≤ i₁)
    (masks : WilsonOlderSignedOneMarkBooked.opening R simple (school.order+school.horizon+2) q₁ 102
      (show 0 < WilsonMeasuredRankedMenu.fee R query.letter.toll M₀ (ε/16)/6 from div_pos (WilsonMeasuredRankedMenu.fee_positive R query.letter.toll M₀ ep₀) (by norm_num)) ≤ i₁)
    (soft : WilsonOlderSignedOneMarkCurrency.opening R simple q₁ (WilsonMeasuredRankedMenu.fee_positive R query.letter.toll M₀ ep₀) ≤ i₁)

    (lowerDate:school.horizon≤R.alloy.B.a.clock.J j)
    (money:WilsonMeasuredLandedCurrency.first R simple≤j)
    (booked:WilsonReceivedMeasuredStampPrice.opening R simple q₁ school.order k
      (ready_order deep) (ready_age aged) ep₀ ≤ i₁)
    (geometry:WilsonOlderFreshGraphPreimageFee.first R simple pace query.letter.toll≤j+1)
    (test:Wallet A) {next:ℝ} (positive:0<next) (small:next≤1) :


    ∃(T:child → slate)(c amp:child → ℝ),
      (∀z:child,0<c z ∧ 0<amp z ∧ (amp z)⁻¹ ≤ 2*βhat*(salary z) ∧
        WilsonOlderFreshGraphDatedSalary.Published R L a depth (i₁+1) w ⟨⟨N,cut⟩,testAt z⟩ (T z)) ∧
    ∃(H:∀z:child,upper z (T z))(F:∀z:child,lower z (T z)),
      (∀z:child,(H z).passport = passports z ∧ (H z).modelIndex = (T z).Roster ∧
        HEq (H z).model ((T z).rows (WilsonOlderFreshGraphPointWallet.point (place z)) A) ∧
        (H z).w = (fun _=>amp z) ∧ (H z).cost = c z ∧ (H z).rent = τ ∧
        Filed R hk D Q₀ π Γ Ψ books ahead A kernel grades school.order school.horizon school.pieces
          floor (birth z (T z)) (H z) (F z)) ∧
      ∀(t:Wallet A)(h:child → ℂ), (∀z,‖h z‖ ≤ rate) → ∃(E:Coefficient F₁ lowerSide)(b:ℝ),
        E.Format base R.family.params rp ∧ E.remBound base rp κ b ∧
        (∀U,E.density base section₁ rp U=(∑z,h z*(down z (T z) t U).part u)-
          ((rp).eval U:ℂ)*(∑z,h z*(Spill.Foundry.uncut (F z).model gl t U).part u)) ∧
        (∀U,((rp).eval U:ℂ)⁻¹*E.density base section₁ rp U =
          actualAverage R.family (N:=N) (fun V=>∑z,h z*(material z (T z) t V)) U-
          ∑z,h z*(Spill.Foundry.uncut (F z).model gl t U).part u) ∧
        ( (∫ U,((rp).eval U:ℂ)⁻¹*E.density base section₁ rp U ∂scene R.family.path N per (j+1)) =
            (∫ V,∑z,h z*(material z (T z) t V) ∂scene R.family.path N per ((j+1)+1))-
              (∫ U,∑z,h z*(Spill.Foundry.uncut (F z).model gl t U).part u ∂scene R.family.path N per (j+1))) ∧
        b+(F₁).coeffSize E.x ≤ (8*ε)*g₀^p*(1+‖Annex.compress dmax f‖):=by
  obtain ⟨T,c,amp,published,H,F,issued,rows⟩:=WilsonOlderFreshGraphFundedHearing.original
    (R:=R) (query:=query) (hk:=hk) (D:=D) (Q₀:=Q₀) (π:=π) (Γ:=Γ) (Ψ:=Ψ) (history:=history)
    (scroll:=scroll) (books:=books) (floor:=floor) (top:=top) (school:=school) (op:=op) (lesson:=lesson)
    (cal:=cal) (ahead:=ahead) (house:=house) (A:=A) (L:=L) (a:=a) (depth:=depth) (w:=w) (f:=f) (base:=base)
    (p:=p) (ep:=ep) (simple:=simple) (cut:=cut) (cap:=cap) (pos:=pos) (bounded:=bounded) (schedule:=schedule)
    (kpos:=kpos) (seats:=seats) (shape:=shape) (phase:=phase) (enrolled:=enrolled) (within:=within)
    (budget:=budget) (high:=high) (space:=space) (path:=path) (month:=month) (narrow:=narrow)
    (M₀:=M₀) (office:=office) (way:=way) (pace:=pace) (prepared:=prepared) (fixed:=fixed)
    (date:=date) (late:=late) (grossDate:=grossDate) (fareDate:=fareDate) (ready:=ready) (deep:=deep) (aged:=aged)
    (opened:=opened) (recalled:=recalled) (masks:=masks) (soft:=soft) (lowerDate:=lowerDate)
    (money:=money) (booked:=booked) (geometry:=geometry) (test:=test) (positive:=positive) (small:=small)
  refine ⟨T,c,amp,published,H,F,issued,?_⟩
  intro t h hw
  obtain ⟨E,b,form,rem,physical,conditional,bill⟩:=rows t h hw
  refine ⟨E,b,form,rem,physical,conditional,?_,bill⟩
  exact WilsonOlderFreshGraphOriginalScene.original R hk D Q₀ π Γ Ψ history scroll books
    house.licence.employed floor house.stamps top school ahead A base cut T F high space
    ((lower_appointment R school).choose_spec j lateScene)
    (fun z=>⟨H z,(issued z).1,(issued z).2.1,(issued z).2.2.1⟩) t h _ conditional
end YM.Integration.WilsonOlderFreshGraphFundedScene
end
