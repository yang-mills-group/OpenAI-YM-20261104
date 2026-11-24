import YM.Integration.FVA1Physical.MixedResets.Vacancy
import YM.Integration.FVA1Physical.MixedResets.Norm
import YM.QuadraticLocal.Tariff.Measure
/-!
# Local lemma: the joint re-expression with its budget

For full disjoint analytic Mark kernels with arbitrary corrections, on the same
native `Lesson`. Here at **predictive (early) presentation** P'. Same reply
before every independent test choice. Norm on the actual signed regular LOG
comparison AND on the full native strong forced portion of the unnormalized
packet. `expenseReal` fixed pre-currency & kernel choices; no extra Ω payments
hidden in valuation of the mark comparison, even for emitted terms proportional
to analytic kernel envelopes (can account by the chosen w throughout the path).
Mark statement is in mixed unextracted conventions (no π-coordinates); force
part of the discrepancy is on the labeled support of the actual K, not by
subtraction from some other supposed non-perturbatively aligned forced model.

Consult `Early.price.rooted` for the complete mixed-reader budget
& `Early.price.reads` using `Early.family` by lowering exponent from +2,
to read: on the same masks and each Wallet, exact exponential of that
regular comparison model with its residual, unchanged all-field force
cost; summability of the WHOLE marked polynomial including every K
combination. Integrability of the actual signed push below. In particular
inserting a non-positive U with a thermal budget does not infer a Mark
identity by taking a log or dividing its evaluated density.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.MixedResets
open Function Filter Finset Lattice RG RG.Supply Precision Wilson Marker
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Ker
open Push ConnectedActivityE6 Input Org PhysicalNext PhysicalNext.Repeat Legato
open Uniform Next.SectorChange ThroughLaunch Pane AbsoluteSums PriceCompiler
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port Progress.ClassicalKin Progress.ClassicalKin.Tent
open Pressure Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset
open Roost Legato Graces Extra.Iteration Extra.Histories
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open Comparison.RG02 Further.PhysicalPeriodLimitF933 Tree
open Oak
open scoped Topology BigOperators Classical

section deletion
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] {I : Marker.Census V} {p : BudgetPoint}
  {o : V → Site n} (Y : QuadraticLocal.Lamps X ι G p o I) {w : V → ℝ} {B : ℕ} {a s : ℝ}
lemma pay_all (paid : (Deletion.sink Set.univ Y).Paid w B a s) : Y.Paid w B a s := by
  let ask : ∀ i t, (Deletion.sink Set.univ Y).nominal t i = Y.nominal t i := fun i t => by rw [Deletion.sink]; exact if_pos (fun j _ => Set.mem_univ _)
  obtain ⟨f,hf,h,h'⟩ := paid.budget
  exact ⟨f,hf,fun i t x hx => (ask i t ▸ h i t x hx),h'⟩
end deletion

variable {G : Gauge} (R : Run G) {m n i k N : ℕ} (J : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) {Ψ : ∀ i, RG.Rep G (R.family.side i n)}
  (conc : Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
  {φ : ℕ → ℕ} (clock : Offices.Books D R.rolls Q φ) (ahead : Mentor.Forecast D R.rolls Q φ clock)
  (hi : m ≤ i) (cut : i<N) (L : Lesson (N:=N) R J D Q π Γ hi)
  (U : RG.Rep G (R.family.side (i+1) n))
set_option quotPrecheck false
local notation "σ" => R.alloy.B.a
local notation "I" => R.alloy.B.a.clock.J i
local notation "I'" => R.alloy.B.a.clock.J (i+1)
attribute [local irreducible] Till.Tilt.sundry
local notation "C" => R.alloy.B.a.budget i
local notation "Fμ" => R.alloy.B.a.budget (i+1)
local notation "Wc" => (Time.quoteHard (σ) i (R.kit.book) U.beta)
local notation "τ" => R.family.path.levels.clock.op i n
local notation "µ" => (τ).ratio
local notation "p₀" => (Burn.horizon k+2)
local notation "g" => Coat.gStep U.beta
local notation "κ" => LocalComparison.forcedDivisor R.family i

variable (cap : QuadraticLocal.Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (hp : RG.Shoot.Lives (WheelP.neutral R.alloy).bake N (i+1) n U)
  (e : ℝ) (seed : Burn.Seed U (WheelP.M0 k 0 (R.alloy.B.a.budget (i+1)) (π (i+1)) U.beta))
  {Θ ι ιw : Type} [Fintype Θ] [DecidableEq Θ] {R₀ : Marker.Census Θ}
  (o : Earn.Passport (R.family.side (i+1) n) Θ) {X : Θ → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℝ (X i)]
  (allow : ∀ i, Set (X i)) (kills : ∀ i, Submodule ℝ (X i))
  (t : Affinity.Wallet allow)
  (M : ι → Earn.Row o R₀ G (Affinity.Wallet allow)) (Z : Tint.Incoming o U (Affinity.Wallet allow) ιw R₀)
  (w : Θ → ℝ) (grades : Θ → ℕ) (p horizon : ℕ) (e_E funds ηz : ℝ) (s : ℕ)
local notation "Mnew" => (o.coarser ((τ).ratio))
local notation "u" => (Poetry.Agenda.seed D φ (Burn.horizon k) I')
local notation "v" => (Poetry.Agenda.seed D φ (Burn.horizon k) I)
local notation "r" => ((p:ℝ)+1-ηz)
local notation "Ω" => Oak.expenseReal R J D Q π Γ clock hi cap L ahead p horizon
local notation "Ωm" => Oak.figureReal R J D Q π Γ clock hi cap L ahead p horizon
local notation "due" => (8*Ω^(cap.count+1)*(e_E+e) + 16 * ((2:ℝ)^ r * (Coat.gStep U.beta)^ r))
variable (F₁ : Tree.Forest (Route.step R i n).ratio)
  (young : Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) p cap.count cap.stage k (R.alloy.B.a.clock.J i))
  {J' : Type} (pre : Locator.Calendar R J D Q π Γ hi L (U:=U) e F₁)
local notation "P'" => (Locator.paneling R J D Q π Γ hi L pre.listing pre.source U.beta pre.scalar)
local notation "out" => Oak.student (n:=n) R J D Q π Γ clock hi cap L ahead allow M p young
variable (next : Tint.Incoming (o.coarser (R.family.path.levels.clock.op i n).ratio) (Locator.paneling R J D Q π Γ hi L pre.listing pre.source U.beta pre.scalar) (Affinity.Wallet allow) J' R₀)
local notation "W" => (Tint.Patrol.report out next (Coat.gStep U.beta))
local notation "Y" => ( Tint.Patrol.picture M Z )
local notation "spent" => (Ω * funds)
local notation "after" => (Ω^2 * funds)
open MeasureTheory
set_option maxHeartbeats 820000
structure Early : Prop where
  ready : (Route.step R i n).IsKernel U.beta G
  actual x : Integrable ((Y).density x) (prior G (R.family.side (i+1) n)) ∧
    (Route.step R i n).push U.beta ((Y).density x) = (W).density x
  price : Full P' w κ next 2 due ((2*g)^(2*s))
  strongest : next.hard.Paid w (C).B (C).supportExponent (Real.sqrt Wc) ∧ Real.sqrt Wc ≤ R.family.path.levels.clock.forcedAllowance i
  tuition : Earn.Scene.Armada out w grades v ((Ωm).produce (µ).count * funds) p cap.count horizon
  family : (Y).E.Paid w U.p.B U.p.supportExponent (spent + e_E) ∧ (W).E.Paid w (C).B ((C).supportExponent+2) (after + due)
  custody : Earn.Tableau kills allow out ∧ Affinity.Taut (Mnew).support allow kills next.old ∧ Affinity.Crown (Mnew).support allow kills next.hard
  forecast : Renderer out (π i) (Step.tape p₀) grades p (Route.wilson R N p₀ (π (i+1)) M p)
  vacancy : Vacancy R J D Q π Γ hi L U e F₁ pre p
  beam : ∃ q : ℕ, Ω ≤ (Delay.fineMonitor G (R.rolls.L I') (R.alloy.B.a.clock.hatBeta i))^q ∧
    (Delay.fineMonitor G (R.rolls.L I') (R.alloy.B.a.clock.hatBeta i))^q ≤ budgetR R i

include F₁ cut pre hp conc
variable [Countable ι] [Countable ιw] [Countable J']

lemma pre_price (hall : Locator.Elementary.Newhall (n:=n) (U:=U) R J D Q π Γ Ψ clock ahead hi cut L e seed p F₁ pre cap allow kills M Z w grades horizon young e_E funds ηz s next Set.univ)
    (earned : Earn.Scene.Armada M w grades u funds p cap.count horizon)
    (old : Z.old.Paid w U.p.B U.p.supportExponent e_E) (full : Z.hard.Paid w U.p.B U.p.supportExponent 1) :
    Early R J D Q π Γ clock ahead hi L U cap e o allow kills M Z w grades p horizon e_E funds ηz s F₁ young pre next := by
  let z := hall.semantic
  let h := z.tale; let a := h.Waffle
  let t := h.earning; let d := due
  have c : 0 ≤ funds := budget_nonneg (earned.suggests 0)
  have hm : 0 ≤ (Ωm).produce (µ).count * funds := budget_nonneg (t.suggests 0)
  have hin := (Lamps.loan_monotone _ ( Scene.Armada.paid _ _ _ earned _ a.breeze )
    (mul_le_mul_of_nonneg_right a.wage c))
  have hin' : (Y).E.Paid w U.p.B U.p.supportExponent (spent+e_E) := Lamps.joinPaid hin old
  have hw x := QuadraticLocal.Tariff.integrable R₀ o.origin w earned.positive Y x ⟨hin', full⟩ U.p.exponent_pos.le hp.valid
  have δ : (C).supportExponent+2 = (C).supportExponent+1+1 := by ring
  have hreg : next.old.Paid w (C).B ((C).supportExponent+2) d := by rw [δ]; exact pay_all _ z.connect
  refine ⟨ (σ).transition_mass .., fun x => ⟨hw x, h.reads x⟩, ?_, z.terrain, t,
    ⟨hin', Lamps.joinPaid ?_ hreg⟩, ⟨h.school,h.repair,h.force⟩,
    (student_renders R D Q J π Γ hi L conc cut clock cap allow M young ahead t).1,
    derive_vacancy R J D Q π Γ conc hi cut L U hp e seed F₁ pre p hall.continuum,z.pantry ⟩
  · exact ⟨(Graces.glyphBound (σ) i).1,earned.positive,hreg,z.photographs⟩
  rw [δ]
  apply Lamps.loan_monotone _ ( Scene.Armada.paid _ _ _ t _ a.soon )
  apply (mul_le_mul_of_nonneg_right a.quote hm).trans
  rw [pow_two,mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right a.earns c) a.paysAbove.le
end YM.Integration.FVA1Physical.MixedResets
