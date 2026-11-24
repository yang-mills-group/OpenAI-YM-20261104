import YM.Integration.WilsonThermometerPostedCompactHard

/-! The original nonbare appointment for the three separately purchased, unmasked compact fields. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace YM.Integration.WilsonThermometerThreeCompactHard
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

include simple course cut cal chamber hospital in
theorem original {b τ cap ticket U ξ:ℝ} (bp:0<b) (purse:b ≤ 1) (payment:b ≤ (Ω)⁻¹)
    (positive:0 < τ) (small:τ ≤ 1) (ticket0:0 ≤ ticket)
    (fares:∀z:I,(∑j,(T z).fare j) ≤ ticket) (charges:∀z:I,‖charge z‖ ≤ cap)
    (unit:∀v (t:ℂ),t∈A v→‖t‖ ≤ 1) (x₀:Wallet A)
    (qorder:q ≤ order) (slots:3 ≤ op.count) (count:op.count ≤ Burn.horizon k+2)
    (fit:(∑v:Fin 3,grades v) ≤ shelf) (level:shelf ≤ R.alloy.B.a.clock.J i) (stage:order+1 ≤ op.stage)
    (size:order+(∑v:Fin 3,grades v) ≤ Burn.horizon k+2)
    (fund:Invoice.Supports (H).p U ((H).p.supportExponent+1) (g) (Poetry.Agenda.seed (G:=G) (U:=R.metals.K) (F:=R.metals.p.profile) (K:=R.metals.p.kernel) D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) ξ)
    (top:Topline (H) (R.family.path.levels.clock.forcedAllowance (i+1))) :
    let size₀:=ceiling I cap ticket
    let fee:=WilsonOriginalThreeCompactWallet.fee G (H).p U (g) ξ order op.count shelf ((∑v:Fin 3,grades v)+1)
    ∃ P:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead A (S₀) grades
        order shelf op.count i hi (physical),
      P.rent=τ ∧ P.cost=(wage) P.w ∧ P.cost ≤ b ∧ P.passport=Passport.point sites ∧
      P.inputIndex=Empty ∧ P.op=op ∧ P.lesson=lesson ∧
      P.modelIndex=Index owner grades T ∧ HEq P.model M ∧
      P.input.hard.Paid P.w (H).p.B (H).p.supportExponent (R.family.path.levels.clock.forcedAllowance (i+1)) ∧
      (∀v,(P.w v)⁻¹=(1+size₀)*(b⁻¹+|fee|/Willow.haloSlack (H).p.B)) ∧
      ∀t (u:Config G (R.family.side (i+1) per)),(Tint.Patrol.picture P.model P.input).density t u=
        ((H).eval u:ℂ) • ∏v:Fin 3,(1+Poly.send ((J).fire v) (value owner
          (fun z=>WilsonOriginalPointCompactFaces.amount owner grades sites T A charge z (g) t u) v)) := by
  let σ:ℝ:=Poetry.Agenda.seed (G:=G) (U:=R.metals.K) (F:=R.metals.p.profile) (K:=R.metals.p.kernel) D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
  have σ0:0≤σ:=fund.2.2.2.2.1
  have past:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J i:=hk.trans (R.alloy.B.a.fits.mono hi)
  have qfits:q ≤ R.alloy.B.a.clock.J i:=qorder.trans ((Nat.le_add_right _ _).trans (size.trans past))
  have table:=@WilsonOriginalPointCompactProgram.tested G (R.family.side (i+1) per) I q σ owner grades sites T A charge
  have voter:=@WilsonOriginalPointCompactVoter.original G (R.family.side (i+1) per) I inferInstance q σ
    owner grades sites T A charge σ0 unit order op.count op.stage k (R.alloy.B.a.clock.J i)
    slots (fit.trans level) qorder qfits stage size
  obtain ⟨sale⟩:=@WilsonOriginalThreeCompactCommission.original G (R.family.side (i+1) per) I inferInstance q σ
    owner grades sites T A charge (H).p b (g) U ξ cap ticket bp ticket0 fares charges σ0 unit order op.count shelf qorder slots fit fund
  exact WilsonThermometerPostedCompactHard.received R simple hk D Q π Γ Ψ course scroll books hi cut op lesson cal
    ahead chamber hospital owner grades sites T A charge order shelf table voter purse payment positive small x₀
    count level sale top

end YM.Integration.WilsonThermometerThreeCompactHard
