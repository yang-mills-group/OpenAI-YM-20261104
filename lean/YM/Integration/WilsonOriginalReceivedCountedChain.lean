import YM.Integration.WilsonOriginalReceivedFiledChain

/-! Countable intake on the very same elected successor, with its original signed field and radius. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalReceivedChain
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

variable {G : Gauge} (R : Run G) {m j N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (floor : m ≤ j)
  (physical : Wallet actors → Config G (R.family.side ((j+1)+1) per) → Poly (Stock.census V))

  (P : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1)
    (floor.trans (Nat.le_succ j)) physical)

local notation "earlier" => (fun x : Wallet actors => LocalComparison.actualPush R.family N per (j+1) (physical x))
local notation "elected" => Oak.expenseReal R hk D Q π Γ books (floor.trans (Nat.le_succ j)) P.op P.lesson ahead order shelf
local notation "g" => Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta

local notation "stud" => Oak.student (n:=per) R hk D Q π Γ books (floor.trans (Nat.le_succ j)) P.op P.lesson ahead actors P.model order P.voter
local notation "origin" => Oak.grade0 R hk D Q π Γ (floor.trans (Nat.le_succ j)) P.lesson
local notation "recorded" => Mutation.stamp stud (Γ (j+1)) origin (Burn.horizon k+2) order
local notation "inherited" => Mutation.grow stud (Γ (j+1)) origin (Burn.horizon k+2) order
  (Coat.gStep (Ψ ((j+1)+1)).beta) (Coat.gStep (Ψ (j+1)).beta) (Ψ (j+1)) P.output

/-- One earlier date of this same history, with its charged radius fixed before its
positive target tolerance. All earlier faces are carried in the filed physical source. -/
theorem next_filed_counted (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (path : PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ) (cut : j+1 < N)
    (pass : Pass D Q R.alloy R.kit) (scroll : VowsR.LawScroll G φ)
    (chamber : VowsR.Chamber scroll R.kit D Q books) (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J j)
    (load : seats ≤ Burn.horizon k+2) (packed : order+shelf ≤ Burn.horizon k+2)
    (simple : G.Simple) (q : ℕ) (deep : 2*q+8 ≤ order) (aged : q+3 ≤ 3*k+2)
    {ε : ℝ} (ep : 0 < ε) (late : WilsonReceivedMeasuredStampPrice.opening R simple q order k deep aged ep ≤ j+1)
    (test : Wallet actors) :
    ∃ (h C E : ℝ) (lesson₂ : Lesson (N:=N) R hk D Q π Γ floor),
      1 ≤ h ∧ C ≤ budgetR R (j+1) ∧ E ≤ P.rent+ε*g^q ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∃ L : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats j floor earlier,
        L.lesson = lesson₂ ∧ (∀ v, L.w v = P.w v/(elected^6*h)) ∧ L.cost = h⁻¹*C ∧ L.rent = max (h⁻¹*E) τ ∧
        h = max 1 (max (Oak.expenseReal R hk D Q π Γ books floor L.op L.lesson ahead order shelf*C) E) ∧
        h ≤ max 1 (max (budgetR R j*budgetR R (j+1)) (P.rent+ε*g^q)) ∧
        Filed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P L ∧ Countable L.inputIndex := by
  letI : Countable P.modelIndex := P.modelCount
  letI : Countable P.outputIndex := P.outputCount
  have nativeLoad : P.op.count ≤ Burn.horizon k+2 := P.capacity.le.trans load
  let plan : Syl.School k := ⟨order,P.op.count,shelf,nativeLoad,fits,packed⟩
  let nx := plan.room (step_paid R.alloy.B.a j) (hk.trans (R.alloy.B.a.fits.mono floor))
  obtain ⟨lesson₂,vote,one,_,cheap,small,fee,cap,count,wallet,funds,school,taut,crown,regular,forced,_,field,issued⟩ :=
    WilsonOriginalReceivedRepeat.purchased R hk D Q π Γ Ψ course books path floor cut P.op P.lesson ahead actors P.model
      P.w grades order shelf P.voter P.cost P.rent pieces P.input P.output pass scroll chamber month hospital fits narrow nativeLoad packed
      P.issued simple q deep aged ep late (Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0)) P.affordable P.active.le test
  refine ⟨_,_,_,lesson₂,one,cap,fee,?_⟩
  intro τ τpos τone
  obtain ⟨idx,idxCount,out,story,stage,_⟩ := issued τ τpos τone
  let L : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats j floor earlier :=
    { op := nx
      capacity := P.capacity
      lesson := lesson₂
      passport := P.passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio
      modelIndex := _
      inputIndex := _
      outputIndex := idx
      modelCount := count
      outputCount := idxCount
      model := _
      input := _
      output := out
      w := _
      cost := _
      rent := _
      affordable := cheap
      active := τpos.trans_le (le_max_right _ _)
      small := max_le small τone
      voter := vote
      salary := funds
      tests := school
      oldTests := taut
      hardTests := crown
      regular := (by exact Lamps.loan_monotone _ regular (le_max_left _ _))
      forced := forced
      represented := fun x => (field x).symm.trans (congrArg (LocalComparison.actualPush R.family N per (j+1)) (P.represented x))
      issued := story }
  let siz := (R.alloy.B.a.S.oneStep (j+1) per).exact_size
  let epoch := Oak.era R hk D Q π Γ (floor.trans (Nat.le_succ j)) P.op P.lesson
  let text := Cruise.publish D R.rolls Q R.alloy φ books P.op epoch siz P.model order P.voter P.lesson.entry
  haveI : Countable (Scene.Texts P.model (Pane.panel R.alloy (j+1) siz).ratio text) :=
    Scene.crewC P.model _ text (Cruise.funded D R.rolls Q R.alloy φ books P.op epoch siz P.model order
      P.voter P.lesson.entry P.lesson.studied ahead)
  have combined : Countable ((Scene.Texts P.model (Pane.panel R.alloy (j+1) siz).ratio text) ⊕ P.outputIndex) :=
    inferInstance
  exact ⟨L,rfl,wallet,rfl,rfl,rfl,stage,⟨rfl,rfl,HEq.rfl,HEq.rfl,HEq.rfl⟩,combined⟩

end YM.Integration.WilsonOriginalReceivedChain
