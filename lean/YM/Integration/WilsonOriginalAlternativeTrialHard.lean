import YM.Integration.WilsonOriginalAlternativeTrialUnary
import YM.Integration.WilsonMeasuredReturnedHardField
import YM.Integration.WilsonFirstReceivedGalleryRegular

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialHard
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


local notation "heat_" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "mode_" j:max => (J_).fire j
local notation "F_" j:max => R.family.labels.level (grades j)
local notation "S_" j:max => R.family.localSection (grades j)
local notation "soft_" j:max U:max => ((gauge).E.log fire_ U).part (mode_ j)
local notation "truth_" j:max => WilsonMeasuredSingletonForce.row (F:=(F_ j)) P.output.hard fire_ j

include course upper in
/-- The actual receiving hard slice heard against its entire original quiet
cofactor, including on the failed configurations of either spectator. -/
theorem original (way:WayStation R.kit) (cutoff:ℕ)
    (active:cutoff+6*seats ≤ R.alloy.B.a.clock.J i) (j:V):
    let h:=truth_ j
    let y:=homes j
    h.Format y R.family.params (W_) ∧
      h.remBound y (W_) κ ((P.w j)⁻¹*heat_^(-(cutoff:ℝ))) ∧
      h.x=0 ∧ h.regular=0 ∧ (∀a U,h.forced a U=(P.output.hard.hard fire_ a U).part (mode_ j)) ∧
      ∀U,h.density y (S_ j) (W_) U/((W_).eval U:ℂ)=(fed_ j) U-(soft_ j U) ∧
        ‖h.density y (S_ j) (W_) U/((W_).eval U:ℂ)‖ ≤
          WilsonOriginalAlternativeTrialSource.cap R grades N per (b+1) v z j+account/(weights j):=by
  intro h y
  have cut:i<N:=lt_of_le_of_lt ib upper
  obtain ⟨fmt,paid,x0,r0,keys,source⟩:=WilsonMeasuredReturnedHardField.original R hk D Q π Γ Ψ books
    ahead actors pieces grades order shelf seats hi (physical) P cut way course cutoff active
    (S_ j) R.family.params fire_ j
  obtain ⟨wp,regularPaid,_⟩:=WilsonCenteredReceivedWages.original R hk D Q π Γ Ψ course books hi cut ahead
    actors pieces grades order shelf seats (physical) P way
  have quiet:(Ψ i).eval=(R.family.path.rep N per i).eval:=(later R π Γ Ψ course hi cut.le).view
  refine ⟨fmt,paid,x0,r0,keys,?_⟩
  intro U
  have measured:=WilsonOriginalAlternativeTrialTravel.one R grades N per b o v z upper ib j U
  have exactSource:=source U
  rw [measured,←quiet,Complex.real_smul] at exactSource
  have nz:((W_).eval U:ℂ)≠0:=by
    rw [quiet]
    exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson cut.le U).ne'
  have equality:h.density y (S_ j) (W_) U/((W_).eval U:ℂ)=(fed_ j) U-(soft_ j U):=by
    apply (div_eq_iff nz).2
    change (truth_ j).density (homes j) (S_ j) (W_) U=_
    linear_combination -exactSource
  have budget:=WilsonFirstReceivedGalleryRegular.occupied (P:=W_) (gauge).E regularPaid
    (by linarith only [(W_).p.exponent_pos]) wp fire_ U (mode_ j) j (Finset.mem_singleton_self _)
  rw [Poly.solo_toll] at budget
  have ordinary:‖soft_ j U‖≤account/(weights j):=by
    apply (le_div_iff₀ (wp j)).2
    exact (mul_comm _ _).le.trans budget
  have measuredCap:=actualTransport_norm_le R.family R.makes upper
    (WilsonOriginalAlternativeTrialSource.salary R grades N per (b+1) o v z j).2 (ib.trans (Nat.le_succ b)) U
  exact ⟨equality,equality ▸ (norm_sub_le _ _).trans (add_le_add measuredCap ordinary)⟩

end YM.Integration.WilsonOriginalAlternativeTrialHard
