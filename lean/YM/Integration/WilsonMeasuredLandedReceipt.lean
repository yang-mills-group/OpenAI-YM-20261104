import YM.Integration.WilsonMeasuredLandedAdvance
import YM.Integration.WilsonOlderFreshGraphHostTarget

/-! One signed advance of the independently registered singleton on its own
physical course. The chosen upper and lower posts retain the original field,
support, regular and forced wallets. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredLandedReceipt
open Push.AbsoluteSums Next.Foundations
open Filter Labels Source Planned.GuardedAtom Push.Local
open WilsonOriginalReceivedChain
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Stationary Comparison.RG02 Comparison.RG02.Order Further.PhysicalPeriodLimitF933 Laurent
open RG16 Pert.Asymptotics WilsonMeasuredRankedResidual
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {m j N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  (school : Syl.School k) (floor : m ≤ j)
  (actors : Unit → Set ℂ) {inputRank : ℕ}
  {passport : Earn.Passport (R.family.side ((j+1)+1) per) Unit}
  {entries : Type} (model : entries → Row passport (Stock.census Unit) G (Wallet actors))
local notation "pieces" => (fun _ : Unit => (⊥ : Submodule ℝ ℂ))
local notation "grades" => (fun _ : Unit => inputRank)
local notation "upper" => (floor.trans (Nat.le_succ j))
local notation "rp" => Ψ (j+1)
local notation "bare" => Ψ ((j+1)+1)
local notation "head" => fun (x:Wallet actors) (U:Config G (R.family.side ((j+1)+1) per)) =>
  ((bare).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut model (Coat.gStep (bare).beta) x U)
local notation "earlier" => (fun x:Wallet actors => LocalComparison.actualPush R.family N per (j+1) (head x))
local notation "upperPost" => Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q π Γ Ψ books ahead
  actors pieces grades school.order school.horizon school.pieces (j+1) upper (head)
local notation "lowerPost" => Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q π Γ Ψ books ahead
  actors pieces grades school.order school.horizon school.pieces j floor earlier
local notation "g" => Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta
local notation "gm" => Pert.Asymptotics.regulatorRun R.family N per m
local notation "y" => (passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin ()
local notation "u" => (Stock.census Unit).fire ()
local notation "κ" => LocalComparison.forcedDivisor R.family (j+1)
variable (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (path:PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ) (cut:j+1<N)
    (pass:Pass D Q R.alloy R.kit) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (narrow:school.horizon≤R.alloy.B.a.clock.J (j+1))
    (fieldRank:ℕ)
local notation "F₀" => R.family.labels.level fieldRank
local notation "S₀" => R.family.localSection fieldRank
local notation "Y₀" => R.family.params

def realized (τ c w:ℝ) (high:ℕ) (limit:ℝ) : Prop :=
  ∃ (H:upperPost) (L:lowerPost),
      H.passport=passport ∧ H.modelIndex=entries ∧ HEq H.model model ∧
      H.w=(fun _=>w) ∧ H.cost=c ∧ H.rent=τ ∧
      (∀ (a:ℝ) (B:ℕ),H.input.old.Paid (fun _=>w) B a 0) ∧
      H.input.hard.Paid (fun _=>w) (bare).p.B (bare).p.supportExponent
        (LocalComparison.forcedDivisor R.family ((j+1)+1)*(R.alloy.B.a.clock.hatBeta ((j+1)+1))^(-(high:ℝ))) ∧
      Filed R hk D Q π Γ Ψ books ahead actors pieces grades
        school.order school.horizon school.pieces floor (head) H L ∧
      ∀ x:Wallet actors,∃ (A:Coefficient F₀ (R.family.side (j+1) per)) (b:ℝ),
        A.Format y Y₀ rp ∧ A.remBound y rp κ b ∧
        (∀ U,A.density y S₀ rp U=(earlier x U).part u-
          ((rp).eval U:ℂ)*(Spill.Foundry.uncut L.model (Coat.gStep (rp).beta) x U).part u) ∧
        b+(F₀).coeffSize A.x≤limit
end YM.Integration.WilsonMeasuredLandedReceipt
end
