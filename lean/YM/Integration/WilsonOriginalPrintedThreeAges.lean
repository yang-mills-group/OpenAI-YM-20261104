import YM.Integration.WilsonOlderFreshThermometerReceipt
import YM.Integration.WilsonOriginalNamedCarriedThree

/-! Two consecutive physical block filings on the same genuine three-name paid post. -/

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace YM.Integration.WilsonOriginalPrintedThreeAges
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open WilsonOriginalPointCompactRoster WilsonOriginalPointCompactCash WilsonOriginalThreeCompactProduct
open WilsonOriginalReceivedChain Extra.Histories MergeProof.Accent Pert.Asymptotics
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m j N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j, RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ → ℕ} (scroll:LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (floor:m ≤ j) (cut:j+1 < N)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J ((j+1)+1)) (R.alloy.B.a.clock.J (j+1)))
  (lesson:Lesson (N:=N) R hk D Q π Γ (floor.trans (Nat.le_succ j)))
  (cal:Oak.Calendar R hk D Q π Γ Ψ (floor.trans (Nat.le_succ j)) (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (chamber:VowsR.Chamber scroll R.kit D Q books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)

local notation "H" => Ψ ((j+1)+1)
local notation "g" => Coat.gStep (H).beta
variable {I:Type} [Fintype I] {q:ℕ} (owner:I→Fin 3) (grades:Fin 3→ℕ)
  (sites:Fin 3→Site (R.family.side ((j+1)+1) per))
  (T:(z:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner z)) q (Poetry.Agenda.seed (G:=G) (U:=R.metals.K) (F:=R.metals.p.profile) (K:=R.metals.p.kernel) D φ (Burn.horizon k) (R.alloy.B.a.clock.J ((j+1)+1))))
  (A:Fin 3→Set ℂ) (charge:I→ℂ) (order shelf:ℕ)
local notation "M" => rows owner grades sites T A charge
local notation "J" => Stock.census (Fin 3)
local notation "S₀" => (fun _:Fin 3=>(⊥:Submodule ℝ ℂ))
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books (floor.trans (Nat.le_succ j)) op lesson ahead order shelf
local notation "wage" => WilsonOriginalPointCompactSalary.invoice owner grades sites T charge
local notation "physical" => (fun t U=>((H).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut M (g) t U))

attribute [local irreducible] Poetry.Agenda.seed


open Pressure MintClock
local notation "width₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J ((j+1)+1))
local notation "χ" => R.alloy.B.a.clock.hatBeta ((j+1)+1)
local notation "heat" => Page.temperature G 1 χ
local notation "billing" => WilsonOriginalThreeCompactWallet.fee G (H).p heat (g) (width₀/4)
    order op.count shelf ((∑v:Fin 3,grades v)+1)


local notation "hi" => floor.trans (Nat.le_succ j)
local notation "earlier" => (fun t:Wallet A=>LocalComparison.actualPush R.family N per (j+1) ((physical) t))
local notation "g₁" => Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta
local notation "prior" => WilsonOriginalNamedCompactCover.declared R cut (π ((j+1)+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2)) (Passport.point sites) (M) grades order

def Joined (cap ticket τ ε:ℝ) (accuracy:ℕ) : Prop :=
  let size₀ := ceiling I cap ticket
  let pole := (∑v:Fin 3,grades v)+1
  ∃ P:Post (N:=N) R hk D Q π Γ Ψ books ahead A (S₀) grades order shelf op.count (j+1) (hi) (physical),
    P.rent=τ ∧ P.cost=(wage) P.w ∧ P.cost ≤ (max 1 Ω)⁻¹ ∧ P.passport=Passport.point sites ∧
    P.inputIndex=Empty ∧ P.op=op ∧ P.lesson=lesson ∧
    P.modelIndex=Index owner grades T ∧ HEq P.model (M) ∧
    P.input.hard.Paid P.w (H).p.B (H).p.supportExponent (R.family.path.levels.clock.forcedAllowance ((j+1)+1)) ∧
    (∀v,(P.w v)⁻¹=(1+size₀)*(max 1 Ω+|billing|/Willow.haloSlack (H).p.B)) ∧
    (∀v,(P.w v)⁻¹ ≤ (1+size₀)*(χ+2^(order+shelf+1+pole)*χ^(pole+Spill.Raffle.pad (order+shelf+1)))) ∧
    (∀t (u:Config G (R.family.side ((j+1)+1) per)),(Tint.Patrol.picture P.model P.input).density t u=
      ((H).eval u:ℂ) • ∏v:Fin 3,(1+Poly.send ((J).fire v) (value owner
        (fun z=>WilsonOriginalPointCompactFaces.amount owner grades sites T A charge z (g) t u) v))) ∧
    ∃(h C E:ℝ)(lesson₂:Lesson (N:=N) R hk D Q π Γ floor),
      1≤h ∧ C≤budgetR R (j+1) ∧ E≤τ+ε*g₁^accuracy ∧
      ∀η:ℝ,0<η → η≤1 →
      ∃L:Post (N:=N) R hk D Q π Γ Ψ books ahead A (S₀) grades order shelf op.count j floor earlier,
        L.lesson=lesson₂ ∧ (∀v,L.w v=P.w v/(Ω^6*h)) ∧ L.cost=h⁻¹*C ∧ L.rent=max (h⁻¹*E) η ∧
        Filed R hk D Q π Γ Ψ books ahead A (S₀) grades order shelf op.count floor physical P L ∧
        WilsonOriginalCarriedThreeStep.FiledRead R hk D Q π Γ Ψ books ahead A (S₀) grades order shelf op.count
          floor physical P L cut prior

include course chamber hospital simple in
theorem original (path:PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ)
    (pass:Pass D Q R.alloy R.kit) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (fits:order≤Burn.horizon k+1)(narrow:shelf≤R.alloy.B.a.clock.J j)
    (load:op.count≤Burn.horizon k+2)(packed:order+shelf≤Burn.horizon k+2)
    (accuracy:ℕ)(deep:2*accuracy+8≤order)(aged:accuracy+3≤3*k+2)
    {ε:ℝ}(ep:0<ε)(late:WilsonReceivedMeasuredStampPrice.opening R simple accuracy order k deep aged ep≤j+1)
    (test:Wallet A) {cap ticket τ:ℝ}
    (issued:WilsonOlderFreshThermometerReceipt.Printed (N:=N) R hk D Q π Γ Ψ books (hi) op lesson ahead
      owner grades sites T A charge order shelf cap ticket τ):
    Joined R hk D Q π Γ Ψ books floor cut op lesson ahead owner grades sites T A charge order shelf cap ticket τ ε accuracy := by
  obtain ⟨P,rent,cost,small,site,blank,event,receipt,keys,same,hard,priced,uniform,fields⟩:=issued
  refine ⟨P,rent,cost,small,site,blank,event,receipt,keys,same,hard,priced,uniform,fields,?_⟩
  obtain ⟨h,C,E,lesson₂,h₁,c₀,e₀,each⟩:=
    WilsonOriginalNamedCarriedThree.original R hk D Q π Γ Ψ books ahead A (S₀) grades order shelf op.count floor
      physical P course path cut pass scroll chamber month hospital fits narrow load packed simple accuracy
      deep aged ep late test (Passport.point sites) (M) site keys same
  refine ⟨h,C,E,lesson₂,h₁,c₀,rent ▸ e₀,?_⟩
  intro η pos bound
  obtain ⟨L,what,w,c,r,_,_,fed,whole⟩:=each η pos bound
  refine ⟨L,what,?_,c,r,fed,whole⟩
  simpa only [event,receipt] using w

end YM.Integration.WilsonOriginalPrintedThreeAges
end
