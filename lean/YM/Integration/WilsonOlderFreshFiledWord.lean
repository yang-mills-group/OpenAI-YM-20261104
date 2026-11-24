import YM.Integration.WilsonOlderFreshWordReversion
import YM.Integration.WilsonCoherentMayerMutationIntake

/-! Adjacent independently filed words on the actual Wilson course, at both measured couplings. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshFiledWord
open WilsonOriginalReceivedChain
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Stationary Comparison.RG02 Comparison.RG02.Order Further.PhysicalPeriodLimitF933 Laurent
open scoped Classical BigOperators

private theorem sameSum {G : Gauge} {n : Side} {V W I J : Type} [DecidableEq V]
    {c : Census V} {pa pb : Earn.Passport n V} (a : I → Row pa c G W) (b : J → Row pb c G W)
    (p : pa=pb) (names : I=J) (model : HEq a b) (g : ℝ) (x : W) (U : Config G n) :
    Summable (fun j=>Spill.raw a g x j U) ↔ Summable (fun j=>Spill.raw b g x j U) := by
  subst pb
  subst J
  cases eq_of_heq model
  rfl

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

variable (L : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats j floor
  (fun x : Wallet actors => LocalComparison.actualPush R.family N per (j+1) (physical x)))
  (file : Filed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P L)
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (cut : j+1 < N)
  (pass : Pass D Q R.alloy R.kit) (month : Scholar.Month R.rolls D Q R.alloy.delay)
  (fits : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J (j+1)) (x : Wallet actors)

local notation "hi" => (floor.trans (Nat.le_succ j))
local notation "depth" => (Burn.horizon k+2)
local notation "tape₀" => AllOrder.Floe.Step.tape depth
local notation "bankNow" => Air.craft L.model (fun v=>(L.model v).paint x) grades (π (j+1)) tape₀
local notation "priorBank" => Air.craft P.model (fun v=>(P.model v).paint x) grades (π ((j+1)+1)) tape₀
local notation "upperBank" => Air.craft stud (fun v=>((stud) v).paint x) grades (π (j+1)) tape₀
local notation "stampedBank" => Air.craft recorded (fun v=>((recorded) v).paint x) grades (π (j+1)) tape₀
local notation "gu" => Coat.gStep (Ψ ((j+1)+1)).beta
local notation "gl" => Coat.gStep (Ψ (j+1)).beta
local notation "older" => R.family.path.rep N per (j+1)
local notation "reverted" => Mutation.mend stud (Ψ (j+1)).p (Γ (j+1)) origin depth order gu gl
local notation "α" => (Ψ (j+1)).p.supportExponent+1+1

include file course cut in
theorem original (U : Config G (R.family.side (j+1) per)) :
    Spill.Foundry.uncut L.model gl x U = Spill.Foundry.uncut recorded gl x U ∧
    Spill.Foundry.uncut L.model gl x U = Integral.markedLog (Coat.gStep (older).beta) U bankNow ∧
    Spill.Foundry.uncut stud gu x U = Integral.markedLog g U upperBank ∧
    HasSum (fun z=>Poly.send ((stud) z).mode ((reverted).nominal x z U))
      (Integral.markedLog g U upperBank-Integral.markedLog (Coat.gStep (older).beta) U bankNow) := by
  have sameModel := WilsonOlderFreshWordReversion.same L.model recorded file.passport file.names file.model
  have gu_eq := (course.1.walk ((j+1)+1) (Nat.le_succ_of_le hi) cut).beta
  have gl_eq := (course.1.walk (j+1) hi cut.le).beta
  have upperPos : 0<gu := by
    rw [gu_eq]
    exact inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  have lowerPos : 0<gl := by
    rw [gl_eq]
    exact inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson (Nat.lt_of_succ_lt cut)))
  have a := WilsonOlderFreshWordReversion.funded stud P.issued.earning (Poetry.Agenda.stem ..)
    x (π (j+1)) tape₀ upperPos.ne' U
  have b := WilsonOlderFreshWordReversion.funded L.model L.salary (Poetry.Agenda.stem ..)
    x (π (j+1)) tape₀ lowerPos.ne' U
  have c := (sameSum L.model recorded file.passport file.names file.model gl x U).mp b.summable
  have h := WilsonOlderFreshWordReversion.reversion stud (Ψ (j+1)).p (Γ (j+1)) origin depth order
    upperPos.ne' lowerPos.ne' x U a.summable c
  have sold : Spill.Foundry.uncut L.model gl x U = Integral.markedLog (Coat.gStep (older).beta) U bankNow := by
    exact b.tsum_eq.trans (congrArg (fun t=>Integral.markedLog (Coat.gStep t) U bankNow) gl_eq)
  have issued : Spill.Foundry.uncut stud gu x U = Integral.markedLog g U upperBank := by
    exact a.tsum_eq.trans (congrArg (fun t=>Integral.markedLog (Coat.gStep t) U upperBank) gu_eq)
  refine ⟨congrFun (congrFun (congrFun sameModel gl) x) U,sold,issued,?_⟩
  rwa [← sold,← issued,sameModel]

include course cut pass month fits narrow in
/-- Measured positive-order fee of the regular, same-mask reversion in the specified all-field sum. -/
theorem masked (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (load : seats≤Burn.horizon k+2) (simple : G.Simple) {η ε : ℝ}
    (positive : 0<η) (unit : η≤1) (allow : 0<ε)
    (opened : WilsonCoherentMayerMutationIntake.firstDate R simple order positive unit allow ≤ j+1) :
    (reverted).Paid P.w (Ψ (j+1)).p.B α (ε*g^((order:ℝ)+1-η)*P.cost) ∧
    (inherited).hard=P.output.hard := by
  have h := WilsonCoherentMayerMutationIntake.original R hk D Q π Γ Ψ course books hi cut P.op P.lesson ahead
    actors P.model P.w grades order shelf P.voter P.cost pieces P.input P.rent P.output pass month hospital
    P.issued (P.capacity.le.trans load) narrow fits (Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0))
    simple positive unit allow opened
  exact ⟨h.2.2.2.1,h.2.1⟩

end YM.Integration.WilsonOlderFreshFiledWord
