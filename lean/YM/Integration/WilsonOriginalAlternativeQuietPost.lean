import YM.Integration.WilsonOriginalAlternativeQuietShelf
import YM.Integration.WilsonOriginalAlternativeSelectedGrant

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeQuietPost
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


variable {E:Type} [Countable E] (o:V→Site (R.family.side (i+1) per))
  (L:Lamps (Wallet actors) E G (Ψ (i+1)).p o (Stock.census V))
local notation "O_" => Passport.point o
local notation "empty_" => (Empty.elim : Empty→Row O_ J_ G (Wallet actors))
local notation "source_" => (fun x U=>((W_).eval U:ℂ) • Poly.pass (L.log x U))

/-- Releasing every old occupied slot returns the literal original quiet hard
at every key.  Its paid weight is independent of the width of the old marked
program.  The new ordinary columns keep their own declared test weights. -/
theorem original (simple:G.Simple) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (scroll:VowsR.LawScroll G φ) (chamber:VowsR.Chamber scroll R.kit D Q books)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (cut:i<N) (load:seats ≤ Burn.horizon k+2) (narrow:shelf ≤ R.alloy.B.a.clock.J i)
    (fire:Wallet actors) (w:V→ℝ) (wp:∀v,0<w v) {τ:ℝ} (pos:0<τ) (small:τ≤1)
    (earned:L.Paid w (W_).p.B (α_+1+1) τ) (tested:Taut (O_).support actors pieces L):
    ∃U:Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor (source_),
      Countable U.inputIndex ∧ U.w=w ∧ U.rent=τ ∧ U.cost=0 ∧ U.passport=O_ ∧ U.op=P.op ∧ U.lesson=P.lesson ∧
      ∀x a W,(U.input.hard.hard x a W)=Poly.bead J_ (((W_).activities.K a W:ℝ):ℂ):=by
  let native:Hard.Rent (W_).activities.forced (W_).activities.K (W_).p α_ κ_:=
    Hard.transfer P.input.hard α_ fire P.forced P.salary.positive
  let Z:=WilsonOriginalAlternativeQuietShelf.intake actors (O_) (W_) native L
  obtain ⟨hard,truth,atOwner⟩:=WilsonOriginalAlternativeQuietShelf.original (w:=w) actors pieces (O_) (W_) native L
  have regular:=Lamps.tenure L w wp earned (show α_≤α_+1+1 by linarith)
  let agenda:=Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
  have salary:Scene.Armada empty_ w grades agenda 0 order P.op.count shelf:=by
    refine ⟨P.salary.toMinistry,wp,fun _=>?_,⟨fun j=>j.elim,fun j=>j.elim⟩,fun j=>j.elim⟩
    exact ⟨fun j=>j.elim,Summable.of_finite,by simp⟩
  have voter:Cruise.Voter empty_ agenda order P.op.count P.op.stage k (R.alloy.B.a.clock.J i):=by
    refine ⟨fun j=>j.elim,P.salary.quota,P.voter.height,fun C=>?_⟩
    obtain ⟨j,-⟩:=C.property.1
    exact j.elim
  have test:Tableau pieces actors empty_:=⟨fun j=>j.elim⟩
  let cal:=Classical.choice (Oak.agrees R hk D Q π Γ Ψ course floor cut P.lesson)
  have aff:0≤(Oak.expenseReal R hk D Q π Γ books floor P.op P.lesson ahead order shelf)⁻¹:=
    ((tsum_nonneg (P.salary.suggests 0).1).trans (P.salary.suggests 0).2.2).trans P.affordable
  obtain ⟨J,counted,out,story⟩:=Oak.Buffered.arrive R simple hk D Q π Γ Ψ course scroll books chamber floor cut
    P.op P.lesson cal ahead hospital actors pieces empty_ Z w grades order shelf voter τ 0
    (P.capacity.trans_le load) narrow salary test fire tested truth regular
    (Hard.mono _ hard (Graces.glyphBound R.alloy.B.a (i+1)).2) zero_le_one pos small
  let U:Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor (source_):=
    ⟨P.op,P.capacity,P.lesson,O_,Empty,E,J,inferInstance,counted,empty_,Z,out,w,0,τ,aff,pos,small,
      voter,salary,test,tested,truth,earned,hard,fun x=>funext (WilsonOriginalAlternativeQuietShelf.field actors
        (O_) (W_) native L wp regular x),story⟩
  exact ⟨U,inferInstanceAs (Countable E),rfl,rfl,rfl,rfl,rfl,rfl,atOwner⟩

end YM.Integration.WilsonOriginalAlternativeQuietPost
