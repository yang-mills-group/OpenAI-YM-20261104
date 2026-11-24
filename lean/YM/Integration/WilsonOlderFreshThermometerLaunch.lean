import YM.Integration.WilsonOlderFreshThermometerOpportunity
import YM.Integration.WilsonOlderFreshHardSite
import YM.Integration.WilsonOriginalCompactRafflePrice

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace YM.Integration.WilsonOlderFreshThermometerLaunch
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open WilsonOriginalPointCompactRoster WilsonOriginalPointCompactCash WilsonOriginalThreeCompactProduct
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m i N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j, RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ → ℕ} (scroll:LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (hi:m ≤ i) (cut:i < N)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (chamber:VowsR.Chamber scroll R.kit D Q books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)

local notation "H" => Ψ (i+1)
local notation "g" => Coat.gStep (H).beta
variable {I:Type} [Fintype I] {q:ℕ} (owner:I→Fin 3) (grades:Fin 3→ℕ)
  (sites:Fin 3→Site (R.family.side (i+1) per))
  (T:(z:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner z)) q (Poetry.Agenda.seed (G:=G) (U:=R.metals.K) (F:=R.metals.p.profile) (K:=R.metals.p.kernel) D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))))
  (A:Fin 3→Set ℂ) (charge:I→ℂ) (order shelf:ℕ)
local notation "M" => rows owner grades sites T A charge
local notation "J" => Stock.census (Fin 3)
local notation "S₀" => (fun _:Fin 3=>(⊥:Submodule ℝ ℂ))
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "wage" => WilsonOriginalPointCompactSalary.invoice owner grades sites T charge
local notation "physical" => (fun t U=>((H).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut M (g) t U))

attribute [local irreducible] Poetry.Agenda.seed


open Pressure MintClock
local notation "width₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "χ" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "heat" => Page.temperature G 1 χ
local notation "billing" => WilsonOriginalThreeCompactWallet.fee G (H).p heat (g) (width₀/4)
    order op.count shelf ((∑v:Fin 3,grades v)+1)

include simple course cut cal chamber hospital in
theorem original {τ cap ticket:ℝ} (positive:0<τ)(small:τ ≤ 1)(cap0:0 ≤ cap)(ticket0:0 ≤ ticket)
    (fares:∀z:I,(∑j,(T z).fare j) ≤ ticket)(charges:∀z:I,‖charge z‖ ≤ cap)
    (unit:∀v(t:ℂ),t∈A v → ‖t‖ ≤ 1)(x₀:Wallet A)
    (qorder:q ≤ order)(slots:3 ≤ op.count)(count:op.count ≤ Burn.horizon k+2)
    (fit:(∑v:Fin 3,grades v) ≤ shelf)(level:shelf ≤ R.alloy.B.a.clock.J i)(stage:order+1 ≤ op.stage)
    (size:order+(∑v:Fin 3,grades v) ≤ Burn.horizon k+2)
    (top:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
    (start:WilsonMeasuredSemesterSubpower.onset R 1 (by norm_num:0<(1:ℝ)) ≤ i):
    let size₀:=ceiling I cap ticket
    let pole:=(∑v:Fin 3,grades v)+1
    ∃ P:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead A (S₀) grades
        order shelf op.count i hi (physical),
      P.rent=τ ∧ P.cost=(wage) P.w ∧ P.cost ≤ (max 1 Ω)⁻¹ ∧ P.passport=Passport.point sites ∧
      P.inputIndex=Empty ∧ P.op=op ∧ P.lesson=lesson ∧
      P.modelIndex=Index owner grades T ∧ HEq P.model M ∧
      P.input.hard.Paid P.w (H).p.B (H).p.supportExponent (R.family.path.levels.clock.forcedAllowance (i+1)) ∧
      (∀v,(P.w v)⁻¹=(1+size₀)*(max 1 Ω+|billing|/Willow.haloSlack (H).p.B)) ∧
      (∀v,(P.w v)⁻¹ ≤ (1+size₀)*(χ+2^(order+shelf+1+pole)*χ^(pole+Spill.Raffle.pad (order+shelf+1)))) ∧
      ∀t (u:Config G (R.family.side (i+1) per)),(Tint.Patrol.picture P.model P.input).density t u=
        ((H).eval u:ℂ) • ∏v:Fin 3,(1+Poly.send ((J).fire v) (value owner
          (fun z=>WilsonOriginalPointCompactFaces.amount owner grades sites T A charge z (g) t u) v)):=by
  intro size₀ pole
  have cost:=WilsonOlderFreshThermometerOpportunity.original (N:=N) R hk D Q π Γ Ψ course scroll books
    hi cut op lesson ahead chamber hospital owner grades sites T A charge order shelf qorder slots count fit level stage size
    unit (δ:=1) zero_lt_one start
  have one:1 ≤ χ:=(R.alloy.B.a.fits.delayed _).le
  have bank:max 1 Ω ≤ χ:=max_le one (by simpa using cost.2)
  have enough:0 < max 1 Ω:=zero_lt_one.trans_le (le_max_left ..)
  let b:ℝ:=(max 1 Ω)⁻¹
  have bp:0<b:=inv_pos.mpr enough
  have purse:b ≤ 1:=inv_le_one_of_one_le₀ (le_max_left ..)
  have rental:b ≤ (Ω)⁻¹:=inv_anti₀ cost.1 (le_max_right ..)
  have room:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J i:=hk.trans (R.alloy.B.a.fits.mono hi)
  have active:=R.alloy.B.a.fits.mono (Nat.le_succ i)
  have raw:=WilsonOriginalCompactRafflePrice.original R warm course (Nat.le_succ_of_le hi) cut
    (jet:=Burn.horizon k) (by omega) (order:=order) (by omega) (shelf:=shelf) (level.trans active)
    (seats:=op.count) (count.trans (room.trans active)) pole
  have proper:=WilsonOlderFreshHardSite.original R chamber.ready D Q π Γ Ψ course chamber.station
    (Nat.le_succ_of_le hi) top cut
  obtain ⟨P,f,h,c,site,birth,event,teach,idx,model,hard,paid,seen⟩:=
    WilsonThermometerThreeCompactHard.original R simple hk D Q π Γ Ψ course scroll books hi cut op lesson cal ahead
      chamber hospital owner grades sites T A charge order shelf bp purse rental positive small ticket0 fares
      charges unit x₀ qorder slots count fit level stage size raw.1 proper
  have shift(v:Fin 3):(P.w v)⁻¹=(1+size₀)*(max 1 Ω+|billing|/Willow.haloSlack (H).p.B):=by
    simpa only [b,inv_inv] using paid v
  refine ⟨P,f,h,c,site,birth,event,teach,idx,model,hard,shift,?_,seen⟩
  intro v
  rw [shift]
  have pay:0 ≤ size₀:=by dsimp [size₀,ceiling];positivity
  exact mul_le_mul_of_nonneg_left (add_le_add bank raw.2) (by linarith)
end YM.Integration.WilsonOlderFreshThermometerLaunch
end
