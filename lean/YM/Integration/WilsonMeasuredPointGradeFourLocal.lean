import YM.Integration.WilsonMeasuredPointBilinear
import YM.Integration.WilsonMeasuredPointStride
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPointGradeFourLocal
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G){m j N per k Q:ℕ}
  (hk:Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q₀:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q₀ φ)
  (chamber:VowsR.Chamber scroll R.kit D Q₀ books) (floor:m ≤ j)

local notation "hi" => (floor.trans (Nat.le_succ j))
local notation "i₁" => (j+1)
variable
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
  (school:Syl.School k)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J ((j+1)+1)) (R.alloy.B.a.clock.J (j+1)))
  (lesson:Lesson (N:=N) R hk D Q₀ π Γ (floor.trans (Nat.le_succ j)))
  (cal:Oak.Calendar R hk D Q₀ π Γ Ψ (floor.trans (Nat.le_succ j)) (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q₀ φ books)
  (hospital:MintClock.Hospital D R.rolls Q₀ R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀"=> Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i₁+1))
variable (y:Site (R.family.side ((j+1)+1) per))
local notation "S"=>WilsonOlderFreshGraphPointWallet.point y
local notation "letterPost"=>Earn.Passport.point (fun _:Unit=>y)

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

variable {dmax:ℕ} (L:Primer.Families R.family) (a:hue G) (depth:(4:ℕ)<dmax)
    (pivot:(R.family.labels.level 4).Index) (f:Studio dmax)
local notation "w₄" => WilsonNeutralBilinearLetters.plain (R.family.labels.level 4) pivot
local notation "Ω₀"=>Oak.expenseReal R hk D Q₀ π Γ books hi op lesson ahead school.order school.horizon

local notation "βhat"=>R.alloy.B.a.clock.hatBeta (i₁+1)
local notation "massF"=>‖f‖

local notation "pieces" => (fun _ : Unit => (⊥ : Submodule ℝ ℂ))
local notation "grades" => (fun _ : Unit => (4:ℕ))
local notation "slate" => WilsonOlderFreshGraphSlate.Copy G (4:ℕ) Q σ₀
local notation "birth" => (fun (T:slate) (x:Wallet A) (U:Config G (R.family.side (i₁+1) per)) =>
  ((Ψ (i₁+1)).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut (T.rows S A) (Coat.gStep (Ψ (i₁+1)).beta) x U))
local notation "down" => (fun (T:slate) (x:Wallet A) => LocalComparison.actualPush R.family N per i₁ (birth T x))
local notation "upper" => (fun (T:slate) => Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead
  A pieces grades school.order school.horizon school.pieces i₁ hi (birth T))
local notation "lower" => (fun (T:slate) => Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead
  A pieces grades school.order school.horizon school.pieces j floor (down T))
local notation "origin₁" => ((letterPost).coarser (R.family.path.levels.clock.op i₁ per).ratio).origin ()
local notation "u" => (Stock.census Unit).fire ()
local notation "p₁" => Ψ i₁
local notation "d₁" => R.family.labels.level (4:ℕ)
local notation "κ" => LocalComparison.forcedDivisor R.family i₁
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N per j

local notation "stride₄" => ((R.family.path.levels.S.block i₁).val:ℝ)^4
local notation "tap" => (↑(stride₄):ℂ)
local notation "readout" => (fun (T:slate) (F:lower T) (x:Wallet A) (U:Config G (R.family.side i₁ per)) =>
  (down T x U).part u - ((p₁).eval U:ℂ)*(Spill.Foundry.uncut F.model (Coat.gStep (p₁).beta) x U).part u)
local notation "source₄" => Source.Coefficient (d₁) (R.family.side i₁ per)

theorem paid (simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)
    (cut:i₁≤ N)(late:WilsonMeasuredLandedCurrency.first R simple≤ j)
    (room:WilsonOlderFreshGraphPreimageFee.first R simple pace 4≤ i₁)
    (T:slate)(F:lower T)(x:Wallet A)(E:source₄){b ε n:ℝ}(q:ℕ)(ep:0≤ε)(np:0≤ n)
    (fmt:E.Format origin₁ R.family.params (p₁))(rem:E.remBound origin₁ (p₁) κ b)
    (read:∀U,E.density origin₁ (R.family.localSection 4) (p₁) U=readout T F x U)
    (paidAt:b+(d₁).coeffSize E.x≤(ε/8)*g₀^(q+2)*n) :
    let Z:=Extra.Histories.stretch tap E
    Z.Format origin₁ R.family.params (p₁) ∧ Z.remBound origin₁ (p₁) κ (stride₄*b) ∧
      (∀U,Z.density origin₁ (R.family.localSection 4) (p₁) U=tap*(readout T F x U)) ∧
      stride₄*b+(d₁).coeffSize Z.x≤ε*g₀^q*n := by
  intro Z
  have ⟨pL,gp,slack⟩:=WilsonMeasuredPointStride.native (per:=per) R simple pace cut late room
  have w:‖tap‖=stride₄:=by rw [Complex.norm_real,Real.norm_of_nonneg pL]
  refine ⟨Extra.Histories.stretch_format _ fmt,?_,?_,?_⟩
  · exact (congrArg (fun v:ℝ=> Z.remBound origin₁ (p₁) κ (v*b)) w).mp
      (Extra.Histories.stretch_rem tap rem)
  · intro U
    rw [show Z.density origin₁ (R.family.localSection 4) (p₁) U=tap*(E.density origin₁ (R.family.localSection 4) (p₁) U)
      from Extra.Histories.stretch_density ..,read]
  · change stride₄*b+(d₁).coeffSize (tap • E.x)≤_
    rw [Extra.Histories.Size.smul,w,←mul_add]
    exact WilsonMeasuredPointStride.rescaled q pL ep gp.le np slack paidAt

def Active (T:WilsonOlderFreshGraphSlate.Copy G 4 Q
    (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J ((j+1)+1)))) (amp c τ expense lim n:ℝ) (high depth:ℕ):Prop:=
  ∃ (H:upper T) (F:lower T),
    H.passport=letterPost ∧ H.modelIndex=T.Roster ∧ HEq H.model (T.rows (WilsonOlderFreshGraphPointWallet.point y) A) ∧
    H.w=(fun _=>amp) ∧ H.cost=c ∧ H.rent=τ ∧
    (∀a b,H.input.old.Paid (fun _=>amp) b a 0) ∧
    H.input.hard.Paid (fun _=>amp) (Ψ (i₁+1)).p.B (Ψ (i₁+1)).p.supportExponent
      (LocalComparison.forcedDivisor R.family (i₁+1)*βhat^(-(high:ℝ))) ∧
    WilsonMeasuredNeutralFiledStock.Stocked R hk D Q₀ π Γ Ψ books ahead A pieces
      school.order school.horizon school.pieces floor (birth T) H F n (τ+expense) depth ∧
    F.rent≤τ+expense ∧
    (∃h C:ℝ, 1≤ h ∧ C≤ budgetR R i₁ ∧
      (∀v,F.w v=H.w v/((Oak.expenseReal R hk D Q₀ π Γ books hi H.op H.lesson ahead school.order school.horizon)^6*h)) ∧
      F.cost=h⁻¹*C) ∧
    ∀x:Wallet A,∃(E:source₄)(b:ℝ),
      E.Format origin₁ R.family.params (p₁) ∧ E.remBound origin₁ (p₁) κ b ∧
      (∀U,E.density origin₁ (R.family.localSection 4) (p₁) U=readout T F x U) ∧
      let Z:=Extra.Histories.stretch tap E
      Z.Format origin₁ R.family.params (p₁) ∧ Z.remBound origin₁ (p₁) κ (stride₄*b) ∧
        (∀U,Z.density origin₁ (R.family.localSection 4) (p₁) U=tap*(readout T F x U)) ∧
        stride₄*b+(d₁).coeffSize Z.x≤ lim

theorem received (simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)(cut:i₁≤ N)
    (late:WilsonMeasuredLandedCurrency.first R simple≤ j)
    (room:WilsonOlderFreshGraphPreimageFee.first R simple pace 4≤ i₁)
    (T:slate)(amp c τ n ε expense:ℝ)(high depth q:ℕ)(np:0≤ n)(ep:0≤ε)
    (original:WilsonMeasuredPointBilinear.Receipt (N:=N) R hk D Q₀ π Γ Ψ books floor school ahead y A
      T amp c τ expense ((ε/8)*g₀^(q+2)*n) n high depth) :
    Active (N:=N) R hk D Q₀ π Γ Ψ books floor school ahead y A T amp c τ expense (ε*g₀^q*n) n high depth := by
  obtain ⟨H,F,hp,names,hm,w,cost,rent,r0,h0,stock,fee,budget,columns⟩:=original
  refine ⟨H,F,hp,names,hm,w,cost,rent,r0,h0,stock,fee,budget,?_⟩
  intro x
  obtain ⟨E,b,fmt,rem,eqn,small⟩:=columns x
  refine ⟨E,b,fmt,rem,eqn,?_⟩
  exact paid (N:=N) R hk D Q₀ π Γ Ψ books floor school ahead y A simple pace cut late room T F x E q ep np fmt rem eqn small

end YM.Integration.WilsonMeasuredPointGradeFourLocal
end
