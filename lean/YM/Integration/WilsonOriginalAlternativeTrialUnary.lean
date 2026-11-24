import YM.Integration.WilsonOriginalAlternativeUnary
import YM.Integration.WilsonOriginalAlternativeTrialTravel

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialUnary
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

variable {G : Gauge} (R : Run G) {m i b N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  (grades : V → ℕ) (order shelf seats : ℕ)
  (o:V→Site (R.family.side (b+1) per)) (v:∀j,R.family.label (grades j)) (z:V→ℂ)
  (ib:i ≤ b) (upper:b+1 ≤ N)

local notation "actors" => (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
local notation "pieces" => (WilsonOriginalAlternativeFiniteSource.sectors (V:=V))
local notation "head_" => WilsonOriginalAlternativeTrialSource.source R grades N per (b+1) o v z
local notation "physical" => WilsonReceivedCloseHistory.history (N:=N) R actors (head_) i ib
variable (P:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
  (WilsonOriginalAlternativeFiniteSource.sectors (V:=V)) grades order shelf seats i hi
  (WilsonReceivedCloseHistory.history (N:=N) R (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
    (WilsonOriginalAlternativeTrialSource.source R grades N per (b+1) o v z) i ib))
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
local notation "modelFee" => Invoice.price (Ψ i).p (fig).mist (order+shelf+1) P.op.count width (fig).limitC G
local notation "oldFee" => Earn.Earnings.hitPrice (fig) G (sheet).ratio.count (Ψ (i+1)).p (Ψ i).p
  (Ω⁻¹*P.cost) (Ω⁻¹*P.rent) (Burn.young (R.alloy.B.a.clock.hatBeta (i+1)) k) oldG
local notation "account" => (Ω^6)⁻¹*(modelFee*((fig).produce (sheet).ratio.count*P.cost)+Ω^P.op.count*oldFee)
local notation "weights" => Stoop.radius P.w (Ω^6)

local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "configuration" => Config G (R.family.side i per)
local notation "value" => LocalComparison.actualPush R.family N per i


local notation "W_" => Ψ i
local notation "J_" => Stock.census V

local notation "fire_" => (WilsonOriginalAlternativeFiniteSource.fired (V:=V))
local notation "active_" j:max => WilsonOriginalAlternativeTrialSource.arm R grades N per (b+1) o v z j
local notation "fed_" j:max => actualTransport R.family (N:=N) (active_ j) (ib.trans (Nat.le_succ b))

include course upper in
/-- All original K owners of the returned fired singleton are in this
coefficient, with its true positive candidate wage and original denominator. -/
theorem original (way:WayStation R.kit) (simple:G.Simple) (late:WilsonCenteredCaptureClock.first R simple ≤ i)
    (j:V) (start:R.family.ref (grades j) ≤ i) :
    let F:=R.family.labels.level (grades j)
    let y:=homes j
    let S:=R.family.localSection (grades j)
    let μ:=Next.Foundations.price G (max (W_).p.order (W_).p.power)
    let sale:=WilsonCenteredGalleryCapture.fare (W_).p S R.family.params weights ((J_).fire j)
      (∅:Finset V) (fun _=>0) {y} 0 account κ (R.alloy.B.a.clock.forcedAllowance i) μ
    ∃ q:Coefficient F (R.family.side i per),
      q.Format y R.family.params (W_) ∧ q.remBound y (W_) κ sale ∧
      (∀U,q.density y S (W_) U=((value) ((physical) fire_) U).part ((J_).fire j)) ∧
      (∀U,q.density y S (W_) U=(W_).eval U • (fed_ j) U) ∧
      (∀U,‖(fed_ j) U‖≤WilsonOriginalAlternativeTrialSource.cap R grades N per (b+1) v z j) ∧
      ∀ probe:Probe G (grades j),probe.2.val=0 → runProbe F probe q.x=(fed_ j) 1:=by
  intro F y S μ sale
  have cut:i<N:=lt_of_le_of_lt ib upper
  obtain ⟨q,_,form,paid,exactly,_,_,_,_,_,probe⟩:=WilsonOriginalAlternativeUnary.original R
    hk D Q π Γ Ψ course books hi cut ahead actors pieces grades order shelf seats (physical) P
    way simple late (grades j) start fire_ j 0
  have quiet:(Ψ i).eval=(R.family.path.rep N per i).eval:=(later R π Γ Ψ course hi cut.le).view
  have measured:∀U,((value) ((physical) fire_) U).part ((J_).fire j)=(W_).eval U • (fed_ j) U:=by
    intro U
    rw [WilsonOriginalAlternativeTrialTravel.one R grades N per b o v z upper ib j U,quiet]
  refine ⟨q,form,paid,exactly,fun U=>(exactly U).trans (measured U),?_,?_⟩
  · intro U
    exact actualTransport_norm_le R.family R.makes upper
      (WilsonOriginalAlternativeTrialSource.salary R grades N per (b+1) o v z j).2 _ U
  · intro a unit
    rw [probe a unit,measured,Complex.real_smul,inv_mul_cancel_left₀]
    rw [quiet]
    exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson cut.le 1).ne'

end YM.Integration.WilsonOriginalAlternativeTrialUnary
