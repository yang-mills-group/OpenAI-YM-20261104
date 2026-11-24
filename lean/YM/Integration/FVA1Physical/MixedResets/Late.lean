import YM.Integration.FVA1Physical.MixedResets.Bilateral
import YM.QuadraticLocal.Relative.Mates
import YM.QuadraticLocal.Tariff.Culture
/-!
# Local lemma on a re-expression of the actual post-reset K

Budget both before and after the model re-expression on the calibrated course.
Even local receipt on ANY tandem chosen before valuation. Can (and in the
iterative use will) also price with the general thermal lemma (same output admits
THAT panel re-expression too). The Ω^powers here on `e_E` are a finite reserve,
not used on unmixed `e`-contraction; here postcal rather than pre, and we're
not asserting moving the smaller `C_J/L` toll through recalibration. On the
actual trajectory unmarked RC after reset has the full higher internal order
budgets already. `Calibrated` annotates costs at BOTH analytic packet-readout weights
& on the true Faculty coupling at A. Use `hβ` below for rephrasing `Gm,G'` in
`Route.coupling`, not a choice of new β from the mark prediction.
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

variable {G : Gauge} (R : Run G) {m n i k N : ℕ} (J : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ i, RG.Rep G (R.family.side i n))
  (conc : Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
  {φ : ℕ → ℕ} (clock : Offices.Books D R.rolls Q φ) (ahead : Mentor.Forecast D R.rolls Q φ clock)
  (hi : m ≤ i) (cut : i<N) (L : Lesson (N:=N) R J D Q π Γ hi)
set_option quotPrecheck false
local notation "σ" => R.alloy.B.a
local notation "I" => R.alloy.B.a.clock.J i
local notation "I'" => R.alloy.B.a.clock.J (i+1)
attribute [local irreducible] Till.Tilt.sundry
local notation "C" => R.alloy.B.a.budget i
local notation "Fμ" => R.alloy.B.a.budget (i+1)
local notation "U" => (Ψ (i+1))
local notation "P'" => (Ψ i)
local notation "Gm" => (Coat.gStep ((Ψ i).beta))
local notation "Wc" => (Time.quoteHard (σ) i (R.kit.book) (Ψ (i+1)).beta)
local notation "τ" => R.family.path.levels.clock.op i n
local notation "µ" => (τ).ratio
local notation "p₀" => (Burn.horizon k+2)
local notation "g" => Coat.gStep (Ψ (i+1)).beta
local notation "κ" => LocalComparison.forcedDivisor R.family i

variable (cap : QuadraticLocal.Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  {Θ ι ιw : Type} [Fintype Θ] [DecidableEq Θ] {R₀ : Marker.Census Θ}
  (o : Earn.Passport (R.family.side (i+1) n) Θ) {X : Θ → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℝ (X i)]
  (allow : ∀ i, Set (X i)) (kills : ∀ i, Submodule ℝ (X i))
  (t : Affinity.Wallet allow)
  (M : ι → Earn.Row o R₀ G (Affinity.Wallet allow)) (Z : Tint.Incoming o (Ψ (i+1)) (Affinity.Wallet allow) ιw R₀)
  (w : Θ → ℝ) (grades : Θ → ℕ) (p horizon : ℕ) (e_E funds ηz : ℝ) (s : ℕ)
local notation "Mnew" => (o.coarser ((τ).ratio))
local notation "u" => (Poetry.Agenda.seed D φ (Burn.horizon k) I')
local notation "v" => (Poetry.Agenda.seed D φ (Burn.horizon k) I)
local notation "r" => ((p:ℝ)+1-ηz)
local notation "Ω" => Oak.expenseReal R J D Q π Γ clock hi cap L ahead p horizon
local notation "Ωm" => Oak.figureReal R J D Q π Γ clock hi cap L ahead p horizon
local notation "due" => (8*Ω^(cap.count+1)*e_E + 16 * ((2:ℝ)^ r * (Coat.gStep (Ψ (i+1)).beta)^ r))
variable (F₁ : Tree.Forest (Route.step R i n).ratio)
  (young : Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) p cap.count cap.stage k (R.alloy.B.a.clock.J i))
  {J' : Type}
local notation "out" => Oak.student (n:=n) R J D Q π Γ clock hi cap L ahead allow M p young
variable (next : Tint.Incoming (o.coarser (R.family.path.levels.clock.op i n).ratio) (Ψ i) (Affinity.Wallet allow) J' R₀)
local notation "W" => (Tint.Patrol.report out next (Coat.gStep (Ψ (i+1)).beta))
local notation "Y" => ( Tint.Patrol.picture M Z )
local notation "spent" => (Ω * funds)
local notation "after" => (Ω^2 * funds)
open MeasureTheory
set_option maxHeartbeats 820000
open Buffered
open QuadraticLocal.Rebirth
local notation "dueCalibrated" => (8*Ω^(cap.count+1)*e_E + 17 * ((2:ℝ)^ r * (Coat.gStep (Ψ (i+1)).beta)^ r))
local notation "new" => ( Mutation.grow out (Γ i) (Oak.grade0 R J D Q π Γ hi L) p₀ p g Gm (Ψ i) next )
local notation "ym" => ( Buffered.born R J D Q π Γ clock hi cap L ahead allow M p young )
local notation "Z'" => ( Tint.Patrol.picture ym new )
local notation "ticket" => ( Oak.rebate R J D Q π Γ hi cap L )
local notation "B" => (Ψ i).p
local notation "A" => (Ψ (i+1)).p
local notation "predict" => Renderer out (π i) (Step.tape p₀) grades p
local notation "receipt" => Renderer ym (π i) (Step.tape p₀) grades p
local notation "preModel" => Route.wilson R N p₀ (π (i+1)) M p
local notation "formal" => Route.reexpress R N p₀ (π (i+1)) M p
local notation "Cal" => Route.calibrator R D Q J π Γ hi L
local notation "Dollars" P:max Lm:max b:max => QuadraticLocal.Lamps.Paid Lm w (P).B ((P).supportExponent+2) b

-- `late` pays on the representation used BEYOND the step; `earned` also
-- on `Λ` generated along the way (same next physical Ψ, pre-reexpression
-- monetary coordinate). Costs for both in one-price original or ephemeral
-- w (if in a history of Learn, use explicit billing below before writing
-- the next Ribbon). All with a fixed reserve (`B` native).
structure Calibrated : Prop where
  currents : (Ψ (i+1)).beta=( R.family.path.rep N n (i+1) ).beta ∧ (Ψ i).beta= (R.family.path.rep N n i).beta
  couplings : g=Route.coupling R N (i+1) n ∧ Gm = Route.coupling R N i n
  kernel : (Route.step R i n).IsKernel (Ψ (i+1)).beta G
  actual x : Integrable ((Y).density x) (prior G (R.family.side (i+1) n)) ∧
    (W).density x = (Route.step R i n).push (Ψ (i+1)).beta ((Y).density x) ∧ ( Z' ).density x = ( W ).density x
  earned : Full (Ψ i) w κ next 2 due ((2*g)^(2*s))
  late : Full (Ψ i) w κ new 2 dueCalibrated ((2*g)^(2*s))
  strongest : (new).hard.Paid w (B).B (B).supportExponent (Real.sqrt Wc)
  wilson : predict preModel ∧ receipt (formal Cal)
  mean : Earn.Scene.Armada out w grades v ((Ωm).produce (µ).count * funds) p cap.count horizon
  renewal : Earn.Scene.Armada ym w grades v (ticket * ((Ωm).produce (µ).count * funds)) p cap.count horizon
  custody : Earn.Tableau kills allow ym ∧ Affinity.Taut (Mnew).support allow kills (new).old ∧ Affinity.Crown (Mnew).support allow kills (new).hard
  billing : (Y).E.Paid w (A).B (A).supportExponent (spent + e_E) ∧
    Dollars B ((W).E) (after + due) ∧ Dollars B ((Z').E) (ticket * after + dueCalibrated)
  geometry : ∃ q : ℕ, Ω ≤ (Delay.fineMonitor G (R.rolls.L I') (R.alloy.B.a.clock.hatBeta i))^q ∧
    (Delay.fineMonitor G (R.rolls.L I') (R.alloy.B.a.clock.hatBeta i))^q ≤ budgetR R i
  torque : ticket ≤ budgetR R i

include cut conc
variable [Countable ι] [Countable ιw]

lemma post_price (story : Tandem (n:=n) R J D Q π Γ Ψ clock hi cap L ahead allow kills M Z w grades p horizon young e_E funds Set.univ next)
    (budget : Phys.Texture (n:=n) R J D Q π Γ Ψ clock hi cap L ahead allow M w p horizon young e_E funds (s:=s) ηz Set.univ next dueCalibrated)
    (earned : Earn.Scene.Armada M w grades u funds p cap.count horizon)
    (old : Z.old.Paid w (A).B (A).supportExponent e_E) (full : Z.hard.Paid w (A).B (A).supportExponent 1) :
    Calibrated R J D Q π Γ Ψ clock ahead hi L cap o allow kills M Z w grades p horizon e_E funds ηz s young next := by
  let h := story.Story; let a := h.Waffle; let b := story.updates; let tx := h.earning
  let book := story.reborn
  let c := later R π Γ Ψ conc hi cut.le
  let y := later R π Γ Ψ conc (Nat.le_succ_of_le hi) cut
  have hh1 := y.beta; have hh2 := c.beta
  have ht : 0 ≤ funds := budget_nonneg (earned.suggests 0)
  have hm' : 0 ≤ (Ωm).produce (µ).count * funds := budget_nonneg (tx.suggests 0)
  have hm'' : 0 ≤ ticket * ((Ωm).produce (µ).count * funds) := budget_nonneg (book.suggests 0)
  have hin := (Lamps.loan_monotone _ ( Scene.Armada.paid _ _ _ earned _ a.breeze ) (mul_le_mul_of_nonneg_right a.wage ht))
  have hin' : (Y).E.Paid w (A).B (A).supportExponent (spent+e_E) := Lamps.joinPaid hin old
  have hw x := QuadraticLocal.Tariff.integrable R₀ o.origin w earned.positive Y x ⟨hin', full⟩ (A).exponent_pos.le y.truep.valid
  have force := budget.bill next.hard rfl
  let σp := ((Ψ i).p.supportExponent+2)
  have δ : (B).supportExponent+2 = (B).supportExponent+1+1 := by ring
  have hb : Dollars B next.old due := by rw [δ]; exact pay_all _ budget.up
  have hd : Dollars B ((new).old) dueCalibrated := by rw [δ]; exact pay_all _ budget.after
  have fee := (Graces.glyphBound (σ) i).1
  refine ⟨⟨hh1,hh2⟩, ⟨congr_arg Coat.gStep (show (Ψ (i+1)).beta=(R.family.path.rep N n (i+1)).beta from hh1),congr_arg Coat.gStep (show (Ψ i).beta=(R.family.path.rep N n i).beta from hh2)⟩,
    (σ).transition_mass .., fun x => ?_, ⟨fee,earned.positive,hb,force.1⟩, ⟨fee,earned.positive,hd,force.1⟩, force.2,
    ?_,tx,book, ⟨story.course,story.taut,story.crown⟩, ⟨hin',Lamps.joinPaid ?_ hb,Lamps.joinPaid ?_ hd⟩,
    budget.relief,story.rebound ⟩
  · refine ⟨hw x, h.reads x |>.symm.trans ?_, (story.speaks x).symm.trans (h.reads x)⟩
    unfold LocalComparison.actualPush; rw [hh1]; rfl
  · exact born_renders R D Q J π Γ hi L conc cut clock cap allow M young ahead grades tx book
      (fun q l => Tutoring.mates R J D Q π Γ Ψ clock hi cap L ahead allow kills M Z w grades p horizon young e_E funds q l next Set.univ story)
  · rw [δ]; apply Lamps.loan_monotone _ (Scene.Armada.paid _ _ _ tx _ a.soon)
    apply (mul_le_mul_of_nonneg_right a.quote hm').trans
    rw [pow_two,mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right a.earns ht) a.paysAbove.le
  rw [δ]; apply Lamps.loan_monotone _ (Scene.Armada.paid _ _ _ book _ b.soon)
  apply (mul_le_mul_of_nonneg_right b.quote hm'').trans
  rw [pow_two,mul_assoc Ω,mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans story.relic.z_quota)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right b.earns ht) b.paysAbove.le
end YM.Integration.FVA1Physical.MixedResets
