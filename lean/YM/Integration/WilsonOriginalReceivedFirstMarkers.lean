import YM.Integration.WilsonOriginalReceivedFirstPost
import YM.Integration.WilsonOriginalFirstJoinProjectedPermit
import YM.Integration.WilsonWindowOriginalHardRadius
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalReceivedFirstMarkers
open WilsonOriginalReceivedChain
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

local notation "PaidDate" => WilsonOriginalReceivedChain.Post (N:=N) (V:=V) (X:=X) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical
variable (P : WilsonOriginalReceivedChain.Post (N:=N) (V:=V) (X:=X) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical)
local instance : Countable P.modelIndex := P.modelCount
variable (simple : G.Simple) (cut : i<N) (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  (scroll : VowsR.LawScroll G φ) (chamber : VowsR.Chamber scroll R.kit D Q books)
  (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  (load : P.op.count ≤ Burn.horizon k+2) (wide : shelf ≤ R.alloy.B.a.clock.J i)
  (test : Wallet actors)
variable [Countable P.inputIndex]
local notation "fine" => Ψ (i+1)
local notation "employed" => WilsonOriginalReceivedFirstPost.evidence R hk D Q π Γ Ψ books ahead actors pieces grades
  order shelf seats i floor physical P simple cut course scroll chamber hospital load wide test
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books floor P.op P.lesson ahead order shelf
variable (funded : WilsonWindowOriginalHardRadius.Booked R.kit) (d:ℕ) (select:(Stock.census V).Mode→Prop)
  (v:V) (contains:∀t, select t→v∈t.val)

/-- The literal old-address withdrawal and its amplified companion from the original no-birth
certificate. The radius test was elected before all positions. -/
noncomputable def terms
  (distant:∀t, select t→∃a∈t.val,∃b∈t.val, d*(4*(fine).p.B+2)+2*(fine).p.B ≤ separation (P.passport.origin a) (P.passport.origin b)) :=
  let filed := employed
  let real := Classical.choose_spec filed.property
  let fee := WilsonWindowOriginalHardRadius.on_roll R funded _ _ (step_paid R.alloy.B.a i)
  Tint.Institute.Permit.first_hearing real d select v contains fee (by exact distant)

local notation "markers" apart₀:max => terms R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical
  P simple cut course scroll chamber hospital load wide test funded d select v contains apart₀
local notation "quote" => Time.quoteHard R.alloy.B.a i R.kit.book (Ψ (i+1)).beta

/-- One raw forced allowance on each original branch at the radius used by the next rebooking. -/
theorem width
  (distant:∀t, select t→∃a∈t.val,∃b∈t.val, d*(4*(fine).p.B+2)+2*(fine).p.B ≤ separation (P.passport.origin a) (P.passport.origin b)) :
    (markers distant).removed.Paid (Stoop.radius P.w (Ω^6)) (Ψ i).p.B (Ψ i).p.supportExponent quote ∧
    (markers distant).raised.Paid (Stoop.radius P.w (Ω^6)) (Ψ i).p.B (Ψ i).p.supportExponent quote := by
  let row := markers distant
  have r0 := row.removed_paid
  have r1 := row.raised_paid
  have same := Scene.Armada.wallet (V:=V) P.w Ω 5 rfl
  exact ⟨same ▸ r0,same ▸ r1⟩

end YM.Integration.WilsonOriginalReceivedFirstMarkers
