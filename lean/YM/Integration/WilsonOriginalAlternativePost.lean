import YM.Integration.WilsonOriginalAlternativeIntake
import YM.Integration.WilsonOriginalAlternativeHosted
import YM.Integration.WilsonMeasuredCourseQuietSlots

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativePost
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

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


def passport {n:Side} {S:Type} (q:Earn.Passport n S) : Earn.Passport n (S×Port) :=
  ⟨q.origin∘Prod.fst, q.support∘Prod.fst, q.wire∘Prod.fst, q.height∘Prod.fst,
    fun i=>q.born i.1, fun i=>q.visits i.1, fun i=>q.room i.1⟩

/-- The signed guard includes the global unit and the true microscopic threshold mask. -/
def page (v:∀j,R.family.label (grades j)) (amp:Wallet actors → V → ℂ)
    (x:Wallet actors) (U:Config G (R.family.side (i+1) per)) (j:V) : ℂ :=
  amp x j * Extra.Histories.part (R.family.localSection (grades j)) (P.passport.origin j) (Ψ (i+1)) U (v j)

theorem original [Nonempty (Wallet actors)] (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (upper : i+1 ≤ N) (ref : ∀ j, R.family.ref (grades j) ≤ i+1) (v:∀j,R.family.label (grades j))
    (amp:Wallet actors → V → ℂ) (ht:∀x j,‖amp x j‖≤1) :
    let o:=P.passport.origin
    let cost:=WilsonOriginalAlternativeGuard.rent R N per (i+1) J_ o grades v P.w α_
    let F:=page R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical P v amp
    ∃ μ:Type, ∃ Z:Tint.Incoming (passport P.passport) (Ψ (i+1)) (Wallet actors) μ (board J_),
      let A:Gallery (Wallet actors) μ (o∘Prod.fst) (Ψ (i+1)) (board J_):=⟨Z.old,Z.hard⟩
      A.Pays (wallet J_ P.w) α_ (2+cost) κ_ ∧
      (∀x h U,Z.hard.hard x h U=inheritAll J_ (P.input.hard.hard x h U)) ∧
      (∀x U,A.density x U=stamped J_ (physical x U) (F x U)) ∧
      ∀x U,(physical x U).part (J_).quiet=((Ψ (i+1)).eval U:ℂ) := by
  dsimp only
  have same: (R.family.path.rep N per (i+1)).p = (Ψ (i+1)).p :=
    (WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course (floor.trans (Nat.le_succ i)) upper).1
  let L:=WilsonOriginalAlternativeHosted.slate R N per (i+1) upper J_ P.passport.origin
    grades ref v amp (Ψ (i+1)) same
  let A:=WilsonOriginalAlternativeGallery.issued (A_) L
  let Z:Tint.Incoming (passport P.passport) (Ψ (i+1)) (Wallet actors) _ (board J_):=⟨A.E,A.K⟩
  have funds:=WilsonOriginalAlternativeHosted.price R N per (i+1) upper J_ P.passport.origin
    grades ref v amp (Ψ (i+1)) same P.w P.salary.positive α_ ht
  have lamps(x:Wallet actors)(U:Config G (R.family.side (i+1) per)):
      L.log x U=ink J_ (page R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical P v amp x U):=by
    have id:=WilsonOriginalAlternativeHosted.field R N per (i+1) upper J_ P.passport.origin grades ref v amp (Ψ (i+1)) same x U
    exact id.trans (congrArg (ink J_) (funext (fun j=>WilsonOriginalAlternativeHosted.primary R N per (i+1) P.passport.origin grades v amp (Ψ (i+1)) same x U j)))
  obtain ⟨paid,exactField⟩:=WilsonOriginalAlternativeIntake.physical_field R hk D Q π Γ Ψ books ahead
    actors pieces grades order shelf seats i floor physical P L _ funds _ lamps
  refine ⟨_,Z,paid,fun _ _ _=>rfl,exactField,?_⟩
  intro x U
  rw [← P.represented]
  exact (A_).same (WilsonOriginalAlternativeIntake.earning R hk D Q π Γ Ψ books ahead actors pieces grades order
    shelf seats i floor physical P) (W_).p.exponent_pos.le P.salary.positive x U

end YM.Integration.WilsonOriginalAlternativePost
