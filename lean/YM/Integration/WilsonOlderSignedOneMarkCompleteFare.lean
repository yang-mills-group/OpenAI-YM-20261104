import YM.Integration.WilsonOlderSignedOneMarkPhysicalFare
import YM.Integration.WilsonOlderSignedOneMarkScalar
import YM.Integration.WilsonOlderSignedOneMarkBooked
import YM.Integration.WilsonCapturedPrimarySection
import YM.Integration.WilsonMatrixOriginalStableInterval

/-! The complete scalar source returned on an enrolled older date.
Both the hard charge and the numerical field coordinate use the same
physical post and its original source wallet. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderSignedOneMarkCompleteFare
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

include course cut in
theorem original (way : WayStation R.kit) (simple : G.Simple)
    (slow : ∀ j, ((R.family.S.block j).val:ℝ)≤Real.log (Lambda R.family.path.levels j))
    (prepared : WilsonReportLampForecast.Ready R.family.path.levels)
    (fixed : (R.family.path.levels.budget i).supportExponent≤100)
    (date : R.t 0 ≤ i) (late : WilsonCenteredCaptureClock.first R simple ≤ i)
    (grossDate : WilsonReceivedSourceGross.opening R simple ≤ i)
    (fareDate : WilsonOlderSignedOneMarkPhysicalFare.opening R simple slow prepared ≤ i)
    (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (shelved : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2)
    (q h p : ℕ) (ready : h+6 ≤ R.alloy.B.a.clock.J i) (deep : 2*(p+1)+8≤order)
    (aged : p+4≤3*k+2) {δ ε : ℝ} (pos : 0<δ) (ep : 0<ε)
    (opened : WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged pos ≤ i)
    (masks : WilsonOlderSignedOneMarkBooked.opening R simple (order+shelf+2) q 102 ep ≤ i)
    (x : Wallet actors) (v : V) :
    let s:=(Stock.census V).fire v
    let y:=homes v
    ∃ (A : Coefficient F₀ (R.family.side i per)) (b : ℝ), A.Format y Y₀ (Ψ i) ∧
      A.remBound y (Ψ i) κ b ∧
      (∀ U, A.density y stencil (Ψ i) U=(LocalComparison.actualPush R.family N per i
        (physical x) U).part s-((Ψ i).eval U:ℂ)*(raw x U).part s) ∧
      (∀ pr : Probe G 0, runProbe F₀ pr A.x=(P.output.old.log x 1).part s) ∧
      Poly.toll P.w s*((F₀).coeffSize A.x+b) ≤
        (sectionCost+base*(gf⁻¹)^4)*(old+δ*gf^p)+2*Real.exp 102*(2*gf^2)^h+ε*gm^q := by
  intro s y
  have budget := (course.1.walk i hi cut.le).truep.point
  have reader := (WilsonCapturedPrimarySection.original R date (Ψ i) budget).1
  have support : (Ψ i).p.supportExponent≤100:=by rw [budget];exact fixed
  let Z : Support (R.family.side i per):={y}
  have here : y∈Z:=Finset.mem_singleton_self _
  have near : separation y y ≤ 0 := (YM.Lattice.separation_self y).le
  obtain ⟨A,fit,bound,fields,read,primary⟩ :=
    WilsonOlderSignedOneMarkScalar.complete R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades
      order shelf seats physical P way simple late p (h+6) ready deep aged pos opened x v Z y here here 0
      near stencil Y₀ reader
  let e:=old+δ*gf^p
  have gn: 0≤gf:=by exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have en:0≤e:=add_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (pow_nonneg P.issued.Waffle.paysAbove.le _)) P.active.le) (mul_nonneg pos.le (pow_nonneg gn _))
  have legal:=WilsonOlderSignedOneMarkPhysicalFare.original R hk D Q π Γ Ψ course books hi cut ahead
    actors pieces grades order shelf seats physical P simple slow prepared fixed grossDate fareDate
    pass hospital shelved load v e en h
  have allowance:= WilsonOlderSignedOneMarkBooked.weighted R hk D Q π Γ Ψ course books hi cut ahead
    actors pieces grades order shelf seats physical P simple grossDate pass hospital shelved load s Z q 102
    (root (Ψ i).p support y) ep masks
  refine ⟨A,_,fit,bound,fields,read,?_⟩
  rw [mul_add, mul_add (Poly.toll P.w s)]
  calc
    _ ≤ sectionCost*e+(base*(gf⁻¹)^4*e+2*Real.exp 102*(2*gf^2)^h+ε*gm^q) :=
      add_le_add primary (add_le_add legal allowance)
    _ = (sectionCost+base*(gf⁻¹)^4)*(old+δ*gf^p)+2*Real.exp 102*(2*gf^2)^h+ε*gm^q := by dsimp only [e];ring

end YM.Integration.WilsonOlderSignedOneMarkCompleteFare
