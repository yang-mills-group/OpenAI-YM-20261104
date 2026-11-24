import YM.Integration.WilsonOriginalCarriedThreeSale
import YM.Integration.WilsonOriginalNamedCompactCover

/-! Two actual all-old conditional transfers of a declared joint source with each upper copy fixed before the post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNamedCarriedThree
open WilsonOriginalReceivedChain WilsonOriginalCopiedHistory
open Extra.Histories MergeProof.Accent Pert.Asymptotics
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Stationary Comparison.RG02 Comparison.RG02.Order Further.PhysicalPeriodLimitF933 Laurent
open FVA1Physical.TwoReset
open scoped Classical BigOperators Topology


variable {G : Gauge} (R : Run G) {m j N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {X : Fin 3 → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : Fin 3 → ℕ)
  (order shelf seats : ℕ) (floor : m ≤ j)
  (physical : Wallet actors → Config G (R.family.side ((j+1)+1) per) → Poly (Stock.census (Fin 3)))

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

local notation "hi" => (floor.trans (Nat.le_succ j))
local notation "depth" => (Burn.horizon k+2)
local notation "tape₀" => AllOrder.Floe.Step.tape depth

theorem original (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (path : PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ) (cut : j+1 < N)
    (pass : Pass D Q R.alloy R.kit) (scroll : VowsR.LawScroll G φ)
    (chamber : VowsR.Chamber scroll R.kit D Q books) (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J j)
    (load : seats ≤ Burn.horizon k+2) (packed : order+shelf ≤ Burn.horizon k+2)
    (simple : G.Simple) (q : ℕ) (deep : 2*q+8 ≤ order) (aged : q+3 ≤ 3*k+2)
    {ε : ℝ} (ep : 0 < ε) (late : WilsonReceivedMeasuredStampPrice.opening R simple q order k deep aged ep ≤ j+1)
    (test : Wallet actors)
    {ι:Type} (o:Passport (R.family.side ((j+1)+1) per) (Fin 3))
    (M:ι→Row o (Stock.census (Fin 3)) G (Wallet actors)) (site:P.passport=o)
    (keys:P.modelIndex=ι) (same:HEq P.model M) :
    let prior:=WilsonOriginalNamedCompactCover.declared R cut (π ((j+1)+1)) tape₀ o M grades order
    ∃ (h C E : ℝ) (lesson₂ : Lesson (N:=N) R hk D Q π Γ floor),
      1 ≤ h ∧ C ≤ budgetR R (j+1) ∧ E ≤ P.rent+ε*g^q ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∃ L : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats j floor earlier,
        L.lesson = lesson₂ ∧ (∀ v, L.w v = P.w v/(elected^6*h)) ∧ L.cost = h⁻¹*C ∧ L.rent = max (h⁻¹*E) τ ∧
        h = max 1 (max (Oak.expenseReal R hk D Q π Γ books floor L.op L.lesson ahead order shelf*C) E) ∧
        h ≤ max 1 (max (budgetR R j*budgetR R (j+1)) (P.rent+ε*g^q)) ∧
        Filed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P L ∧
        WilsonOriginalCarriedThreeStep.FiledRead R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P L cut prior := by
  intro prior
  have bank:=WilsonOriginalReceivedCopiedCover.published (R:=R) (P:=P) (course:=course) (cut:=cut)
  exact WilsonOriginalCarriedThreeSale.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf
    seats floor physical P course path cut pass scroll chamber month hospital fits narrow load packed simple q
    deep aged ep late test prior (fun t grid div d hd z=>WilsonOriginalNamedCompactCover.paid R cut
      (π ((j+1)+1)) tape₀ o M grades order P.model stud site keys same bank t grid div d hd z)

end YM.Integration.WilsonOriginalNamedCarriedThree
