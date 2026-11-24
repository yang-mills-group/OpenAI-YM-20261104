import YM.Integration.WilsonThermometerReunitedIncome

/-! Renew one physical Post at its three individual source widths, paying its full original forced array once. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerReunitedPost
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
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (cut : i < N)
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
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "fine" => Ψ (i+1)
local notation "σf" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "κf" => LocalComparison.forcedDivisor R.family (i+1)
local notation "αf" => (fine).p.supportExponent
open WilsonPrecontactSeparatedLamps

include cut course in
theorem original (simple : G.Simple) (scroll : VowsR.LawScroll G φ)
    (chamber : VowsR.Chamber scroll R.kit D Q books)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (load : seats ≤ Burn.horizon k+2) (shelfFit : shelf ≤ R.alloy.B.a.clock.J i)
    (sample : Wallet actors) [Countable P.inputIndex]
    (w : V → ℝ) (positive : ∀v, 0 < w v)
    (fee debt : V → ℝ) (joint mixedDebt τ : ℝ)
    (single : ∀v, Offers (fun j : {l // WilsonOriginalOneColor.visible v (P.model l).mode} =>
      P.model j.val) w (σf) (fee v))
    (mixedModel : Offers (fun j : {l // 1 < (P.model l).mode.val.card} =>
      P.model j.val) w (σf) joint)
    (singleOld : ∀v, (WilsonOriginalOneColor.lamps v P.input.old).Paid w (fine).p.B
      (αf+1+1) (debt v))
    (mixedOld : (portion P.input.old (mixed P.input.old)).Paid w (fine).p.B
      (αf+1+1) mixedDebt)
    (covered : P.input.hard.Paid w (fine).p.B αf κf)
    (wage : joint+∑ v,fee v ≤ Ω⁻¹) (rent : mixedDebt+∑ v,debt v ≤ τ)
    (active : 0 < τ) (small : τ ≤ 1) :
    ∃ L : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces
        grades order shelf seats i hi physical,
      L.w=w ∧ L.cost=joint+∑ v,fee v ∧ L.rent=τ ∧ L.op=P.op ∧ L.lesson=P.lesson ∧
      L.passport=P.passport ∧ L.modelIndex=P.modelIndex ∧ HEq L.model P.model ∧
      L.inputIndex=P.inputIndex ∧ HEq L.input P.input ∧ HEq L.voter P.voter ∧
      Countable L.inputIndex ∧ ∀ t U,
      (Tint.Patrol.report (Oak.student (n:=per) R hk D Q π Γ books hi L.op L.lesson ahead actors
        L.model order L.voter) L.output (oldG)).density t U =
      (Tint.Patrol.report (student) P.output (oldG)).density t U := by
  letI := P.modelCount
  obtain salary := WilsonThermometerReunitedIncome.credential P.model P.salary positive
    (WilsonThermometerReunitedIncome.offers P.model fee joint single mixedModel)
  have regular := P.input.old.loan_monotone
    (WilsonThermometerReunitedIncome.regular P.input.old debt mixedDebt singleOld mixedOld) rent
  have cheap : joint+∑ v,fee v ≤ 1 := wage.trans (inv_le_one_of_one_le₀ (by linarith [P.issued.Waffle.strong]))
  have base := Lamps.tenure P.input.old w positive regular (show αf ≤ αf+1+1 from by linarith)
  have allowance := (Graces.glyphBound R.alloy.B.a (i+1)).2
  let cal := Classical.choice (Oak.agrees R hk D Q π Γ Ψ course hi cut P.lesson)
  obtain ⟨J, counted, out, post⟩ :=
    Oak.Buffered.arrive R simple hk D Q π Γ Ψ course scroll books chamber hi cut
      P.op P.lesson cal ahead hospital actors pieces P.model P.input w grades order shelf P.voter τ
      (joint+∑ v,fee v) (P.capacity.trans_le load) shelfFit salary P.tests sample P.oldTests
      P.hardTests base (Hard.mono _ covered allowance) cheap active small
  let L : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces
      grades order shelf seats i hi physical := {
    op := P.op
    capacity := P.capacity
    lesson := P.lesson
    passport := P.passport
    modelIndex := P.modelIndex
    inputIndex := P.inputIndex
    outputIndex := J
    modelCount := P.modelCount
    outputCount := counted
    model := P.model
    input := P.input
    output := out
    w := w
    cost := joint+∑ v,fee v
    rent := τ
    affordable := wage
    active := active
    small := small
    voter := P.voter
    salary := salary
    tests := P.tests
    oldTests := P.oldTests
    hardTests := P.hardTests
    regular := regular
    forced := covered
    represented := P.represented
    issued := post }
  refine ⟨L,rfl,rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl,rfl,HEq.rfl,HEq.rfl,
    inferInstanceAs (Countable P.inputIndex),?_⟩
  intro t U
  have fromL := WilsonOriginalReceivedChain.report R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical L t
  have fromP := WilsonOriginalReceivedChain.report R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical P t
  exact congrFun (fromL.symm.trans fromP) U

end YM.Integration.WilsonThermometerReunitedPost
