import YM.Integration.WilsonOriginalAlternativeSelectedInventory
import YM.Integration.WilsonOriginalAlternativeCounted

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeSelectedGrant
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


open WilsonOriginalAlternativePost

variable (zero:∀j,0∈actors j) (c:V→Port) {E:Type}
    (L:Lamps (Wallet actors) E G (Ψ (i+1)).p P.passport.origin (Stock.census V))
local notation "roster_" => WilsonOriginalAlternativeRetestedIncome.row actors zero c ∘ P.model
local notation "Z_" => WilsonOriginalAlternativeSelectedInventory.joined actors zero c P.input L
local notation "Y_" => fun x=>(Tint.Patrol.picture roster_ Z_).density x
local notation "Ω_" => Oak.expenseReal R hk D Q π Γ books floor P.op P.lesson ahead order shelf

def reserve (old guard rent:ℝ):ℝ:=max 1 ((old+guard)/rent)

theorem original [Countable E] (counted:Countable P.inputIndex) (simple:G.Simple)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (scroll:VowsR.LawScroll G φ) (chamber:VowsR.Chamber scroll R.kit D Q books)
    (cut:i<N) (cal:Oak.Calendar (N:=N) R hk D Q π Γ Ψ floor P.lesson)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (load:seats ≤ Burn.horizon k+2) (narrow:shelf ≤ R.alloy.B.a.clock.J i)
    (fire:Wallet actors) (e:ℝ)
    (added:L.Paid P.w (W_).p.B (α_+1+1) e) (tested:Taut P.passport.support actors pieces L)
    {τ:ℝ} (pos:0<τ) (small:τ ≤ 1):
    let h:=reserve P.rent e τ
    ∃U:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor (Y_),
      Countable U.inputIndex ∧ U.w=Stoop.radius P.w h ∧ U.rent=τ ∧ U.cost=h⁻¹*P.cost ∧
      U.passport=P.passport ∧ U.op=P.op ∧ U.lesson=P.lesson ∧ HEq U.input (Z_) ∧ HEq U.model roster_ := by
  intro h
  have ample:1 ≤ h:=le_max_left .. 
  have posH:0<h:=zero_lt_one.trans_le ample
  have enough:h⁻¹*(P.rent+e) ≤ τ:=by
    rw [inv_mul_le_iff₀ posH]
    exact (div_le_iff₀ pos).mp (le_max_right ..)
  letI : Countable P.inputIndex:=counted
  letI : Countable P.modelIndex:=P.modelCount
  have old:=WilsonOriginalAlternativeSelectedInventory.paid actors zero c P.input L P.regular P.forced added
  have rule:=WilsonOriginalAlternativeSelectedInventory.registered actors pieces zero c P.input L P.oldTests P.hardTests tested
  have voted:=WilsonOriginalAlternativeRetestedIncome.voter actors zero c P.model P.voter
  have salary:=(WilsonOriginalAlternativeRetestedIncome.salary actors zero c P.model P.salary).stored ample
  have tableau:=WilsonOriginalAlternativeRetestedIncome.tableau actors pieces zero c P.model P.tests
  have extra:=(Z_).old.loan_monotone (Stoop.tighten P.w _ P.salary.positive ample old.1) enough
  have hard:=Stoop.leaves P.w _ P.salary.positive ample old.2
  have reg:=Lamps.tenure _ _ salary.positive extra (show α_ ≤ α_+1+1 by linarith)
  have reserveK:κ_ ≤ 1:=(Graces.glyphBound R.alloy.B.a (i+1)).2
  have non:=Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0)
  have aff :h⁻¹*P.cost ≤ (Ω_)⁻¹:=(mul_le_of_le_one_left non (inv_le_one_of_one_le₀ ample)).trans P.affordable
  have strong:4 ≤ Ω_:=MintClock.Page.roofers ..
  have unit:h⁻¹*P.cost ≤ 1:=aff.trans (inv_le_one_of_one_le₀ (by linarith only [strong]))
  obtain ⟨J,hJ,out,post⟩:=Oak.Buffered.arrive R simple hk D Q π Γ Ψ course scroll books chamber floor cut
    P.op P.lesson cal ahead hospital actors pieces roster_ Z_ _ grades order shelf voted τ (h⁻¹*P.cost)
    (P.capacity.trans_le load) narrow salary tableau fire rule.1 rule.2 reg (Hard.mono _ hard reserveK) unit pos small
  let U:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor (Y_):=
    ⟨P.op,P.capacity,P.lesson,P.passport,P.modelIndex,P.inputIndex⊕E,J,P.modelCount,hJ,roster_,Z_,out,
      Stoop.radius P.w h,h⁻¹*P.cost,τ,aff,pos,small,voted,salary,tableau,rule.1,rule.2,extra,hard,fun _=>rfl,post⟩
  exact ⟨U,inferInstanceAs (Countable (P.inputIndex⊕E)),rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl,HEq.rfl⟩

end YM.Integration.WilsonOriginalAlternativeSelectedGrant
