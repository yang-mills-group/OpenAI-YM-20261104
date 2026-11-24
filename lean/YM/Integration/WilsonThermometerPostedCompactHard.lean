import YM.Integration.WilsonThermometerRestoredCompactHard
import YM.Integration.WilsonOriginalThreeCompactCommission

/-! The original nonbare appointment for the three separately purchased, unmasked compact fields. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace YM.Integration.WilsonThermometerPostedCompactHard
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
theorem received (table:Tableau (S₀) A M)
    (voter:Cruise.Voter M (Poetry.Agenda.seed (G:=G) (U:=R.metals.K) (F:=R.metals.p.profile) (K:=R.metals.p.kernel) D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) order op.count op.stage k (R.alloy.B.a.clock.J i))
    {b τ cap ticket U ξ:ℝ} (purse:b ≤ 1) (payment:b ≤ (Ω)⁻¹)
    (positive:0 < τ) (small:τ ≤ 1) (x₀:Wallet A)
    (count:op.count ≤ Burn.horizon k+2) (level:shelf ≤ R.alloy.B.a.clock.J i)
    (sale:WilsonOriginalThreeCompactCommission.Sale owner grades sites T A charge (H).p b (g) cap ticket
      (WilsonOriginalThreeCompactWallet.fee G (H).p U (g) ξ order op.count shelf ((∑v:Fin 3,grades v)+1))
      order op.count shelf)
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
  intro size₀ fee
  obtain ⟨P,w,r,c,o,empty,index,month,names,model,plain⟩:=WilsonThermometerRestoredCompactHard.original R simple hk D Q
    π Γ Ψ course scroll books hi cut op lesson cal ahead chamber hospital (V:=Fin 3) (ι:=Index owner grades T) (X:=fun _:Fin 3=>ℂ) (Passport.point sites) A (S₀)
    M (fun v=>sale.raw v/sale.shrink) grades order shelf voter count level
    (b:=(wage) (fun v=>sale.raw v/sale.shrink)) (τ:=τ)
    (bill:=fee*((wage) sale.raw)) (shrink:=sale.shrink) (initial:=sale.raw) sale.stock table x₀ (sale.paid.trans purse) (sale.paid.trans payment)
    positive small top sale.raw_pos sale.one rfl sale.gross sale.restored
  refine ⟨P,r,?_,c.le.trans sale.paid,o,empty,index,month,names,model,plain,?_,?_⟩
  · exact c.trans (congrArg (wage) w.symm)
  · exact fun v=>(congrArg (fun pick:Fin 3→ℝ=>(pick v)⁻¹) w).trans (sale.inverse v)
  · intro t u
    apply (congrFun (P.represented t) u).trans
    exact congrArg (fun y=>((H).eval u:ℂ) • y) (sale.held t u)

end YM.Integration.WilsonThermometerPostedCompactHard
