import YM.Integration.WilsonOlderSignedOneMarkStep

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnerBlank
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
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "gauge" => (Tint.Patrol.report student P.output oldG)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "width" => ((Ψ i).p.supportExponent+1+1)

local notation "weights" => Stoop.radius P.w (Ω^6)
local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "debt" => (⟨P.output.old,P.output.hard⟩ :
  Gallery (Wallet actors) P.outputIndex homes (Ψ i) (Stock.census V))
local notation "βhat" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "gf" => Coat.gStep (R.family.path.rep N per (i+1)).beta


/-- The original student's entire outgoing paint is financed by the incoming model cost. -/
theorem silent (cost : P.cost=0) (x : Wallet actors) (j : _) : ((student) j).paint x=0 := by
  let X:=student
  have G₁:=P.issued.earning
  let a:=G₁.suggests (X j).center
  have price:Poly.toll P.w (X j).mode * (X j).height (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)) ≤ 0 := by
    simpa [cost,X] using (a.2.1.le_tsum j (fun n _=>a.1 n)).trans a.2.2
  have bounds : (X j).salary≤0 := by
    by_contra! positive
    exact (not_lt_of_ge price) (mul_pos (Poly.worth G₁.positive _) (mul_pos positive (Real.exp_pos _)))
  exact norm_le_zero_iff.mp ((G₁.honor j x).trans bounds)

/-- The genuinely rendered student vanishes also on the failed sheets. -/
theorem original (cost : P.cost=0) (x : Wallet actors) (U : Config G (R.family.side i per)) :
    (lamps).log x U=0 := by
  have row (j:_) : (lamps).frame j x U=0 := by
    have z:=silent R hk D Q π Γ Ψ books hi ahead actors pieces grades order shelf seats physical P cost x j
    simp [QuadraticLocal.Lamps.frame,QuadraticLocal.Lamps.light,QuadraticLocal.Earn.rendered,Row.nominal,z,RG.masked,Set.indicator]
  simp [QuadraticLocal.Lamps.log,row]

end YM.Integration.WilsonMeasuredOwnerBlank
