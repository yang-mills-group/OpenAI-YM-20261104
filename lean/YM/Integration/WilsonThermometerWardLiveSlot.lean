import YM.Integration.WilsonThermometerWardIndividualOneColor

/-! Sparse cap-four source admission on an arbitrary issued incoming post, with its full original marked and quiet store. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerWardLiveSlot
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

local notation "incoming" => Tint.Patrol.picture P.model P.input
local notation "αf" => (Ψ (i+1)).p.supportExponent
local notation "αc" => (Ψ i).p.supportExponent
local notation "κf" => LocalComparison.forcedDivisor R.family (i+1)
local instance : Countable P.modelIndex:=P.modelCount
local instance : Countable P.outputIndex:=P.outputCount
open WilsonOriginalOneColor

theorem entered (v:V) :
    (WilsonOriginalOneColor.lamps v P.input.old).Paid P.w (Ψ (i+1)).p.B (αf+1+1) P.rent ∧
    (hard v P.input.hard).Paid P.w (Ψ (i+1)).p.B αf κf ∧
    (WilsonOriginalOneColorGallery.gallery v incoming).Pays P.w αf 2 κf ∧
    ∀t U,(WilsonOriginalOneColorGallery.gallery v incoming).density t U=WilsonOriginalOneColor.cut v (physical t U):=by
  have hp:=P.salary.positive
  have cost:=P.issued.Waffle.converted (Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0)) P.affordable
  have old:=Lamps.tenure _ P.w hp P.regular (show αf≤αf+1+1 from by linarith)
  have analytic:=Scene.Armada.paid P.model P.w grades P.salary (Ψ (i+1)).p P.issued.Waffle.breeze
  have monthly:=Lamps.joinPaid analytic old
  have earned:(incoming).Pays P.w αf 2 κf:=
    ⟨(incoming).E.loan_monotone monthly ((add_le_add cost.fits P.small).trans_eq (by norm_num)),P.forced⟩
  refine ⟨WilsonOriginalOneColor.regular v _ P.regular,WilsonOriginalOneColor.paid v _ hp P.forced,
    WilsonOriginalOneColorGallery.paid v _ hp earned,fun t U=>?_⟩
  rw [WilsonOriginalOneColorGallery.original v _ hp (Ψ (i+1)).p.exponent_pos.le earned t U,P.represented t]

end YM.Integration.WilsonThermometerWardLiveSlot
