import YM.Integration.WilsonOlderSignedOneMarkCompleteFare
import YM.Integration.WilsonOlderSignedOneMarkCurrency

/-! The original singleton residual in reporting units. The charged source
includes the value of its scalar and its complete original regular and hard
remainder. Only the incoming paid rent is inherited. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderSignedOneMarkPaid
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


local notation "stages" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "raw" x:max U:max => Integral.markedLog gf U
  (Air.craft student (fun b=>(student b).paint x) grades (π i) stages)


open Pert.Asymptotics RG16 WilsonOlderSignedOneMarkTariff
local notation "Y₀" => R.family.params
local notation "stencil" => R.family.localSection 0
local notation "base" => 2*Real.exp 102*(1+2*charge Y₀ stencil)
local notation "F₀" => R.family.labels.level 0
local notation "sectionCost" => testPrice F₀
local notation "gm" => regulatorRun R.family N per m
local notation "old" => (8*Ω^P.op.count)*P.rent


def expense {G : Gauge} (R : Run G) : ℝ :=
  testPrice (R.family.labels.level 0)+
    2*Real.exp 102*(1+2*charge R.family.params (R.family.localSection 0))

private theorem costs {G : Gauge} (R : Run G) :
    0≤testPrice (R.family.labels.level 0) ∧
    0 < 2*Real.exp 102*(1+2*charge R.family.params (R.family.localSection 0)) := by
  refine ⟨zero_le_one.trans (probe_budget (R.family.labels.level 0)).choose_spec.choose_spec.1,?_⟩
  unfold charge
  positivity

theorem positive {G : Gauge} (R : Run G) : 0 < expense R := add_pos_of_nonneg_of_pos (costs R).1 (costs R).2

def intake {G : Gauge} (R : Run G) (q : ℕ) (ε : ℝ) : ℝ := ε/(3*expense R*(2:ℝ)^q)

theorem intake_pos {G : Gauge} (R : Run G) (q : ℕ) {ε : ℝ} (ep : 0 < ε) : 0 < intake R q ε :=
  div_pos ep (mul_pos (mul_pos (by norm_num) (positive R)) (pow_pos (by norm_num) q))

include course cut in
theorem original (way : WayStation R.kit) (simple : G.Simple)
    (slow : ∀ j, ((R.family.S.block j).val:ℝ) ≤ Real.log (Lambda R.family.path.levels j))
    (prepared : WilsonReportLampForecast.Ready R.family.path.levels)
    (fixed : (R.family.path.levels.budget i).supportExponent ≤ 100)
    (date : R.t 0 ≤ i) (late : WilsonCenteredCaptureClock.first R simple ≤ i)
    (grossDate : WilsonReceivedSourceGross.opening R simple ≤ i)
    (fareDate : WilsonOlderSignedOneMarkPhysicalFare.opening R simple slow prepared ≤ i)
    (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (shelved : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2)
    (q : ℕ) (ready : q+1+6 ≤ R.alloy.B.a.clock.J i) (deep : 2*(q+4+1)+8 ≤ order)
    (aged : q+4+4 ≤ 3*k+2) {ε : ℝ} (ep : 0 < ε)
    (opened : WilsonFirstReceivedEarnedFee.opening R simple P.op.count (q+4) order k deep aged
      (intake_pos R q ep) ≤ i)
    (masks : WilsonOlderSignedOneMarkBooked.opening R simple (order+shelf+2) q 102
      (show 0 < ε/3 by positivity) ≤ i)
    (soft : WilsonOlderSignedOneMarkCurrency.opening R simple q ep ≤ i)
    (x : Wallet actors) (v : V) :
    let s:=(Stock.census V).fire v
    let y:=homes v
    ∃ (A : Coefficient F₀ (R.family.side i per)) (b : ℝ), A.Format y Y₀ (Ψ i) ∧
      A.remBound y (Ψ i) κ b ∧
      (∀ U, A.density y stencil (Ψ i) U=(LocalComparison.actualPush R.family N per i
        (physical x) U).part s-((Ψ i).eval U:ℂ)*(raw x U).part s) ∧
      (∀ pr : Probe G 0, runProbe F₀ pr A.x=(P.output.old.log x 1).part s) ∧
      Poly.toll P.w s*((F₀).coeffSize A.x+b) ≤ expense R*(gf⁻¹)^4*old+ε*gm^q := by
  intro s y
  have maskPos : 0 < ε/3 := by positivity
  obtain ⟨A,b,fit,paid,fields,probes,receipt⟩ :=
    WilsonOlderSignedOneMarkCompleteFare.original R hk D Q π Γ Ψ course books hi cut ahead actors
      pieces grades order shelf seats physical P way simple slow prepared fixed date late grossDate fareDate
      pass hospital shelved load q (q+1) (q+4) ready deep aged (intake_pos R q ep)
      maskPos opened masks x v
  refine ⟨A,b,fit,paid,fields,probes,receipt.trans ?_⟩
  obtain ⟨hg,ht,relative,price⟩:=WilsonOlderSignedOneMarkCurrency.measured R simple hi cut q ep soft
  have wage : 0 ≤ old := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg P.issued.Waffle.paysAbove.le _))
    P.active.le
  have budget : expense R*intake R q ε*(2:ℝ)^q ≤ ε/3:=by
    unfold intake
    exact (by field_simp [(positive R).ne'] : expense R*(ε/(3*expense R*(2:ℝ)^q))*(2:ℝ)^q = ε/3).le
  exact WilsonOlderSignedOneMarkCurrency.paid q hg ht (intake_pos R q ep).le wage (costs R).1
    (costs R).2.le relative price budget

end YM.Integration.WilsonOlderSignedOneMarkPaid
