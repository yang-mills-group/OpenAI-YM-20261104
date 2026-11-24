import YM.Integration.WilsonOriginalAlternativeCounted
import YM.Integration.WilsonOriginalAlternativeHearing

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeStamped
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open WilsonOriginalAlternativeNames WilsonOriginalAlternativeExtraction WilsonOriginalAlternativeHearing
open scoped Classical BigOperators

/-- A single before-field receipt for the original, guarded, and signed complete
numerators, uniformly at every older held field and every choice of the other tags. -/
def Heard {G:Gauge} (C:Family G) (N per k:ℕ) {V μ T:Type} [Fintype V] [DecidableEq V]
    (J:Census V) {W:Rep G (C.side k per)} {o:V→Site (C.side k per)} (A:Gallery T μ (o∘Prod.fst) W (board J))
    (F:T → Config G (C.side k per) → Poly J) (B:T → Config G (C.side k per) → V → ℂ) : Prop :=
  ∀x f (lower:f ≤ k) (U:Config G (C.side f per)) (s:J.Mode),
    let g(c:V→Port):=held C N per (source C per J A x c s) lower U
    g (fun _=>0)=held C N per (fun W'=>(F x W').part s) lower U ∧
    g (fun _=>1)=held C N per (fun W'=>(W.eval W':ℂ)*∏v∈s.val,B x W' v) lower U ∧
    g (fun _=>2)=held C N per (fun W'=>∑a:J.Mode,∑b:J.Mode,if Poly.merges a b s then
      (F x W').part a*(∏v∈b.val,-B x W' v) else 0) lower U ∧
    ∀v∈s.val,∀c:V→Port,g (Function.update c v 2)=g (Function.update c v 0)-g (Function.update c v 1)

variable {G : Gauge} (R : Run G) {m N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats i : ℕ) (floor : m ≤ i)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))


open WilsonOriginalReceivedChain WilsonOriginalAlternativeNames WilsonOriginalAlternativePurse
open WilsonOriginalAlternativeExtraction
open scoped Classical BigOperators
variable (P : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical)
local notation "J_" => Stock.census V
local notation "A_" => Tint.Patrol.picture P.model P.input
local notation "W_" => Ψ (i+1)
local notation "α_" => (W_).p.supportExponent
local notation "κ_" => LocalComparison.forcedDivisor R.family (i+1)


open WilsonOriginalAlternativePost

theorem original [Nonempty (Wallet actors)] (counted:Countable P.inputIndex)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (upper : i+1 ≤ N) (ref : ∀ j, R.family.ref (grades j) ≤ i+1)
    (v:∀j,R.family.label (grades j)) (amp:Wallet actors → V → ℂ) (ht:∀x j,‖amp x j‖≤1) :
    let o:=P.passport.origin
    let cost:=WilsonOriginalAlternativeGuard.rent R N per (i+1) J_ o grades v P.w α_
    let F:=page R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical P v amp
    ∃ μ:Type, ∃ Z:Tint.Incoming (passport P.passport) (Ψ (i+1)) (Wallet actors) μ (board J_),
      let A:Gallery (Wallet actors) μ (o∘Prod.fst) (Ψ (i+1)) (board J_):=⟨Z.old,Z.hard⟩
      Countable μ ∧ A.Pays (wallet J_ P.w) α_ (2+cost) κ_ ∧
      (∀x h U,Z.hard.hard x h U=inheritAll J_ (P.input.hard.hard x h U)) ∧
      (∀x U,A.density x U=stamped J_ (physical x U) (F x U)) ∧
      Heard R.family N per (i+1) J_ A physical F := by
  obtain ⟨μ,Z,hc,paid,hard,field,quiet⟩:=WilsonOriginalAlternativeCounted.original R hk D Q π Γ Ψ books ahead
    actors pieces grades order shelf seats i floor physical P counted course upper ref v amp ht
  letI : Countable μ:=hc
  let A:Gallery (Wallet actors) μ (P.passport.origin∘Prod.fst) (Ψ (i+1)) (board J_):=⟨Z.old,Z.hard⟩
  refine ⟨μ,Z,hc,paid,hard,field,?_⟩
  intro x f lower U s
  have raw:=WilsonOriginalAlternativeHearing.entries R.family N per J_ A x (physical x) _ (field x) (quiet x) s lower
  refine ⟨congrFun raw.1 U,congrFun raw.2.1 U,congrFun raw.2.2 U,?_⟩
  intro j hj c
  exact WilsonOriginalAlternativeHearing.exchange R.family N per J_ A x
    (WilsonOriginalAlternativePurse.positive J_ P.salary.positive) paid (Ψ (i+1)).p.exponent_pos.le
    (course.1.walk (i+1) (floor.trans (Nat.le_succ i)) upper).truep.valid (physical x) _ (field x) c j s hj lower U

end YM.Integration.WilsonOriginalAlternativeStamped
