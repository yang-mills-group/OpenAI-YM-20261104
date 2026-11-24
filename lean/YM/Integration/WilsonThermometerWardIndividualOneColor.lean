import YM.Integration.WilsonThermometerWardIndividualHistory
import YM.Integration.WilsonOriginalOneColorGallery
import YM.Integration.WilsonOlderSignedOneMarkStep

/-! The single addressed source and its original old K on both sides of one
actual paid post. The signed regular debt is separated from its analytic return. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerWardIndividualOneColor
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

theorem entered [Countable P.inputIndex] (v:V) :
    (WilsonOriginalOneColor.lamps v P.input.old).Paid P.w (Ψ (i+1)).p.B (αf+1+1) P.rent ∧
    (hard v P.input.hard).Paid P.w (Ψ (i+1)).p.B αf κf ∧
    (WilsonOriginalOneColorGallery.gallery v incoming).Pays P.w αf 2 κf ∧
    ∀t U,(WilsonOriginalOneColorGallery.gallery v incoming).density t U=WilsonOriginalOneColor.cut v (physical t U):=by
  have hp:=P.salary.positive
  have cost:=P.issued.Waffle.converted (Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0)) P.affordable
  have old:=Lamps.tenure _ P.w hp P.regular (show αf≤αf+1+1 from by linarith)
  obtain ⟨B,_⟩:=Tint.Campus.Investor.pays P.model P.input P.w hp grades P.salary cost.breeze
    (show _ ≤ 2-P.rent from cost.fits.trans (by linarith [P.small]))
    ((mul_le_of_le_one_left (by positivity) cost.fits).trans cost.past) old P.forced
  have earned:=Travel.pays incoming P.w B
  refine ⟨WilsonOriginalOneColor.regular v _ P.regular,WilsonOriginalOneColor.paid v _ hp P.forced,
    WilsonOriginalOneColorGallery.paid v _ hp earned,fun t U=>?_⟩
  rw [WilsonOriginalOneColorGallery.original v _ hp (Ψ (i+1)).p.exponent_pos.le earned t U,P.represented t]

include course cut in
theorem returned (way:WayStation R.kit) (simple:G.Simple) (p q:ℕ)
    (ready:q≤R.alloy.B.a.clock.J i) (deep:2*(p+1)+8≤order) (aged:p+4≤3*k+2)
    {ε:ℝ} (ep:0<ε) (opened:WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged ep ≤ i)
    (v:V):
    let e:=(Ω^6)⁻¹*((8*Ω^P.op.count)*P.rent+ε*gf^p)
    let h:=βhat^(-(q:ℝ))*κ
    (WilsonOriginalOneColor.lamps v P.output.old).Paid weights (Ψ i).p.B (αc+2) e ∧
    (hard v P.output.hard).Paid weights (Ψ i).p.B αc h ∧
    ∃ E:ℝ,(WilsonOriginalOneColorGallery.gallery v gauge).Pays weights αc E h ∧
      ∀t U,(WilsonOriginalOneColorGallery.gallery v gauge).density t U=
        WilsonOriginalOneColor.cut v (LocalComparison.actualPush R.family N per i (physical t) U):=by
  intro e h
  have hp:=P.issued.earning.positive
  have one:1≤Ω^6:=one_le_pow₀ P.issued.Waffle.cool
  have positive:∀j,0<weights j:=fun j=>div_pos (hp j) (zero_lt_one.trans_le one)
  have shrink:=Stoop.tighten P.w _ hp one P.issued.tuition
  have inc:=WilsonReceivedInheritedFee.original R hk D Q π Γ Ψ books hi cut P.op P.lesson ahead actors P.model
    P.w grades order shelf P.voter P.cost pieces P.input P.rent P.output P.issued simple p deep aged ep opened
  have regular:P.output.old.Paid weights (Ψ i).p.B (αc+2) e:=by
    simpa only [add_assoc,one_add_one_eq_two] using P.output.old.loan_monotone shrink
      (mul_le_mul_of_nonneg_left inc (inv_nonneg.mpr (zero_le_one.trans one)))
  have force:=P.output.hard.mono P.issued.kept (QuadraticLocal.Advent.force_bill R way π Γ Ψ course hi cut ready)
  have lampPay:=Scene.Armada.paid student P.w grades P.issued.earning (Ψ i).p P.issued.Waffle.soon
  have aggregate:=Lamps.joinPaid lampPay P.issued.tuition
  have a:=Stoop.tighten P.w _ hp one (Lamps.tenure _ P.w hp aggregate (show αc≤width from by linarith))
  have earned:(gauge).Pays weights αc _ h:=⟨a,force⟩
  refine ⟨WilsonOriginalOneColor.regular v _ regular,WilsonOriginalOneColor.paid v _ positive force,_,
    WilsonOriginalOneColorGallery.paid v _ positive earned,fun t U=>?_⟩
  rw [WilsonOriginalOneColorGallery.original v _ positive (Ψ i).p.exponent_pos.le earned t U]
  exact congrArg (WilsonOriginalOneColor.cut v) (congrFun (WilsonOriginalReceivedChain.report R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical P t) U).symm

end YM.Integration.WilsonThermometerWardIndividualOneColor
