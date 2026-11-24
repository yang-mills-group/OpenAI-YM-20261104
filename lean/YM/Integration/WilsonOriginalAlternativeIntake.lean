import YM.Integration.WilsonOriginalReceivedPost
import YM.Integration.WilsonOriginalAlternativeGallery

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeIntake
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

theorem earning [Nonempty (Wallet actors)] : (A_).Pays P.w α_ 2 κ_ := by
  letI : Countable P.modelIndex := P.modelCount
  have hp:=P.salary.positive
  have cost:=P.issued.Waffle.converted (Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0)) P.affordable
  have old:=Lamps.tenure _ P.w hp P.regular (show α_ ≤ α_+1+1 from by linarith)
  have analytic:=Scene.Armada.paid P.model P.w grades P.salary (W_).p P.issued.Waffle.breeze
  exact ⟨(A_).E.loan_monotone (Lamps.joinPaid analytic old)
    ((add_le_add cost.fits P.small).trans_eq (by norm_num)),P.forced⟩

theorem physical_field [Nonempty (Wallet actors)] {μ:Type}
    (L:Lamps (Wallet actors) μ G (W_).p (P.passport.origin∘Prod.fst) (board J_))
    (c:ℝ)(salary:L.Paid (wallet J_ P.w) (W_).p.B α_ c)
    (F:Wallet actors → Config G (R.family.side (i+1) per) → V → ℂ)
    (guards: ∀x U,L.log x U=ink J_ (F x U)) :
    (WilsonOriginalAlternativeGallery.issued (A_) L).Pays (wallet J_ P.w) α_ (2+c) κ_ ∧
    ∀x U,(WilsonOriginalAlternativeGallery.issued (A_) L).density x U=stamped J_ (physical x U) (F x U) := by
  have h:=earning R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical P
  refine ⟨WilsonOriginalAlternativeGallery.price _ _ P.salary.positive h salary,?_⟩
  intro x U
  exact (WilsonOriginalAlternativeGallery.original _ _ P.salary.positive (W_).p.exponent_pos.le h salary x U _ (guards x U)).trans
    (congrArg (fun z=>stamped J_ z (F x U)) (congrFun (P.represented x) U))

end YM.Integration.WilsonOriginalAlternativeIntake
