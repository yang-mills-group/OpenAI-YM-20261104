import YM.Integration.WilsonOriginalReceivedCarryPrice
import YM.Integration.WilsonOriginalFreshJoinedRows

/-! The returned physical logarithm at the new measured coupling. Its full signed
reversion error remains in the old regular portfolio. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusRestamp
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2   ≤   R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m   ≤   i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)

local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter


open QuadraticLocal.Rebirth WilsonRootedKioskOccupiedSlip
local notation "vac" => Ψ i
local notation "gf" => Coat.gStep (Ψ (i+1)).beta
local notation "gc" => Coat.gStep (vac).beta
local notation "gu" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "h₀" => Burn.horizon k+2
local notation "ζ" => Oak.grade0 R hk D Q π Γ hi P.lesson
local notation "stamped" => Mutation.stamp (student) (Γ i) (ζ) (h₀) order
local notation "carried" => Mutation.grow (student) (Γ i) (ζ) (h₀) order (gf) (gc) (vac) P.output
local notation "mend" => Mutation.mend (student) (vac).p (Γ i) (ζ) (h₀) order (gf) (gc)
local notation "agenda" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "w₂" => Stoop.radius P.w ((Ω)^6)
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "a₂" => (vac).p.supportExponent+1+1
local notation "L" => rendered (stamped) (vac).p (gc)
local notation "loan" => Invoice.price (vac).p (fig).mist (order+shelf+1) P.op.count (a₂) (fig).limitC G
local notation "pole" => (∑v:V,grades v)+1
local notation "κ" => LocalComparison.forcedDivisor R.family i

include course cut in
theorem original (simple:G.Simple)(way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)
    (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1)(narrow:shelf ≤ R.alloy.B.a.clock.J i)(slots:P.op.count ≤ h₀)
    (q:ℕ)(deep:2*q+8 ≤ order)(aged:q+3 ≤ 3*k+2){ε:ℝ}(ep:0<ε)
    (late:WilsonReceivedMeasuredStampPrice.opening R simple q order k deep aged ep ≤ i) :
    ∃C:ℝ, C ≤ budgetR R i ∧ Scene.Armada (stamped) (w₂) grades (agenda) C order P.op.count shelf ∧
      Invoice.Supports (vac).p (fig).mist (a₂) (gc) (agenda) (fig).limitC ∧
      (L).Paid (w₂) (vac).p.B (a₂) ((loan)*C) ∧
      Gross (L) (w₂) (vac).p.B (a₂) ((2^(order+shelf+1)/(gc)^(pole))*((loan)*C)) ∧
      (carried).old.Paid (w₂) (vac).p.B (a₂) (P.rent+ε*(gu)^q) ∧
      (carried).hard.Paid (w₂) (vac).p.B (vac).p.supportExponent (κ) ∧
      (carried).old=(mend).join P.output.old ∧ (carried).hard=P.output.hard ∧
      (∀t,((rendered (student) (vac).p (gf)).join P.output.old).log t=((L).join (carried).old).log t) ∧
      ∀t,LocalComparison.actualPush R.family N per i (physical t)=(Tint.Patrol.picture (stamped) (carried)).density t:=by
  letI:Countable P.modelIndex:=P.modelCount
  obtain ⟨salary,_,_,_,old,hard,ident,field⟩:=WilsonOriginalReceivedMeasuredCarry.measured R hk D Q π Γ Ψ
    course books hi cut P.op P.lesson ahead actors P.model P.w grades order shelf P.voter P.cost pieces
    P.input P.rent P.output pass month hospital fits narrow slots P.issued
  obtain ⟨debt,limit,raw,_⟩:=WilsonOriginalReceivedCarryPrice.charged R hk D Q π Γ Ψ course books hi cut
    P.op P.lesson ahead actors P.model P.w grades order shelf P.voter P.cost pieces P.input P.rent P.output
    pass way month hospital fits narrow slots P.issued simple q deep aged ep late
    (budget_nonneg (P.salary.suggests 0)) P.affordable P.active.le
  have cal:=(WilsonOriginalMeasuredReentry.credited R hk D Q pass π Γ Ψ course hi cut P.lesson books P.op ahead
    month order shelf fits narrow).1
  have funds:=WilsonOriginalMeasuredReentry.connected R hk D Q pass π Γ Ψ course hi cut P.lesson books P.op ahead
    month order shelf hospital P.voter.height narrow slots
  have positive:0 ≤ (a₂):=by linarith only [(vac).p.exponent_pos]
  have sourced:∀t:(Stock.census V).Mode,(∑v∈t.val,grades v)+1  ≤  (pole):=fun _=>Nat.succ_le_succ
    (Finset.sum_le_sum_of_subset_of_nonneg (f:=grades) (Finset.subset_univ _) (fun _ _ _=>Nat.zero_le _))
  refine ⟨_,limit,salary,funds.soon,Scene.Armada.paid (stamped) (w₂) grades salary (vac).p funds.soon,
    WilsonMarkedFixedPoleGross.landed (stamped) (w₂) grades (vac).p salary funds.soon (pole) sourced,
    (carried).old.loan_monotone old debt,?_,rfl,ident,?_,?_⟩
  · exact Hard.mono (carried).hard hard raw
  · intro t
    funext U
    exact Mutation.syllable (student) (Γ i) (ζ) (h₀) order (gf) (gc) (Stoop.radius P.w (Ω)) grades
      cal (P.issued.earning.stored P.issued.Waffle.cool) funds.bloom.le positive (vac) P.output
      P.issued.Waffle.soon funds.soon P.issued.local_ t U
  · intro t
    exact (congrArg (LocalComparison.actualPush R.family N per i) (P.represented t).symm).trans (field t)

end YM.Integration.WilsonOriginalCensusRestamp
end
