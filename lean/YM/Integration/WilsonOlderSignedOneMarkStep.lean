import YM.Integration.WilsonOlderSignedSingletonFare
import YM.Integration.WilsonCenteredReceivedAggregate
import YM.Integration.WilsonReceivedInheritedFee

/-! The regular debt and the entire hard return of one genuine occupied mode
on the original received course. The analytic student is removed before the
remaining rows and their compatible quiet partners are paid. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderSignedOneMarkStep
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

include course cut in
theorem original (way : WayStation R.kit) (simple : G.Simple)
    (late : WilsonCenteredCaptureClock.first R simple ≤ i) (p q : ℕ)
    (ready : q ≤ R.alloy.B.a.clock.J i) (deep : 2*(p+1)+8 ≤ order)
    (aged : p+4 ≤ 3*k+2) {ε : ℝ} (ep : 0<ε)
    (opened : WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged ep ≤ i)
    (x : Wallet actors) (v : V) (Z : Support (R.family.side i per)) (y : Site (R.family.side i per))
    (center : y∈Z) (member : homes v∈Z) (rad : ℕ) (near : separation (homes v) y≤rad)
    {d : ℕ} {F : Labels.Frame G d} (S : SectionData F) (Y : Hol G) {μ : ℝ}
    (reader : Readable Y S (Ψ i).p (R.family.side i per) μ) :
    let s := (Stock.census V).fire v
    let toll := WilsonOlderSignedSingletonFare.fare (Ψ i).p S Y weights s 1 Z rad
      ((Ω^6)⁻¹*((8*Ω^P.op.count)*P.rent+ε*gf^p)) (βhat^(-(q:ℝ))*κ) κ
      (R.alloy.B.a.clock.forcedAllowance i) μ
    ∃ A : Coefficient F (R.family.side i per), A.Format y Y (Ψ i) ∧
      A.remBound y (Ψ i) κ toll ∧ ∀ U, A.density y S (Ψ i) U =
        (LocalComparison.actualPush R.family N per i (physical x) U).part s -
        ((Ψ i).eval U:ℂ)*((lamps).log x U).part s := by
  intro s toll
  have hp:=P.issued.earning.positive
  have one : 1≤Ω^6:=one_le_pow₀ P.issued.Waffle.cool
  have positive : ∀j,0<weights j:=fun j=>div_pos (hp j) (lt_of_lt_of_le zero_lt_one one)
  have shrink:=Stoop.tighten P.w _ hp one P.issued.tuition
  have inc:=WilsonReceivedInheritedFee.original R hk D Q π Γ Ψ books hi cut P.op P.lesson ahead actors P.model
    P.w grades order shelf P.voter P.cost pieces P.input P.rent P.output P.issued simple p deep aged ep opened
  have regular : P.output.old.Paid weights (Ψ i).p.B ((Ψ i).p.supportExponent+2)
      ((Ω^6)⁻¹*((8*Ω^P.op.count)*P.rent+ε*gf^p)) :=by
    have larger:=P.output.old.loan_monotone shrink (mul_le_mul_of_nonneg_left inc (inv_nonneg.mpr (zero_le_one.trans one)))
    simpa only [add_assoc,one_add_one_eq_two] using larger
  have force:=P.output.hard.mono P.issued.kept (QuadraticLocal.Advent.force_bill R way π Γ Ψ course hi cut ready)
  obtain ⟨K⟩:=WilsonCenteredCourseKeeper.original R course i hi cut
  have actual:=(course.1.walk i hi cut.le).truep
  obtain ⟨div,pos,room⟩:=(eventually_atTop.mp (WilsonCenteredCaptureClock.original R simple)).choose_spec i late
  rw [←actual.point] at room
  obtain ⟨A,form,bill,field⟩:=WilsonOlderSignedSingletonFare.original debt x v 1 weights positive
    regular force div pos room (Ψ i).p.exponent_pos.le actual.valid K Z y center member rad near S Y reader
  refine ⟨A,form,bill,fun U=>?_⟩
  have aw:=QuadraticLocal.Earn.Scene.Armada.paid student P.w grades P.issued.earning (Ψ i).p P.issued.Waffle.soon
  have win : 0≤width :=by linarith only [(Ψ i).p.exponent_pos]
  have hs:=aw.sums win hp x U
  have hr:=P.issued.tuition.sums win hp x U
  have hj:=(Lamps.joinPaid aw P.issued.tuition).sums win hp x U
  have hd:=Hard.packet_summing P.output.hard force (Ψ i).p.exponent_pos.le positive x U
  have report:=congrFun (WilsonOriginalReceivedChain.report R hk D Q π Γ Ψ books ahead actors pieces grades order shelf
    seats i hi physical P x) U
  rw [field]
  change 1*((debt).density x U).part ((Stock.census V).fire v) = _ - _
  rw [one_mul,report]
  change ((debt).density x U).part ((Stock.census V).fire v) =
    ((gauge).density x U).part ((Stock.census V).fire v) - _
  rw [WilsonCenteredSingletonMass.ordinary debt x U v hr hd,
      WilsonCenteredSingletonMass.ordinary gauge x U v hj hd]
  have join : ((gauge).E.log x U).part s = ((lamps).log x U).part s+(P.output.old.log x U).part s :=
    congrArg (fun W : Poly (Stock.census V)=>W.part s) (Lamps.joinLog x U hs hr)
  let a : ℂ := (Ψ i).eval U
  let b : ℂ := (Real.exp ((Ψ i).exponent U):ℂ)*((debt).gas x U).part s
  change a*(P.output.old.log x U).part s+b=a*((gauge).E.log x U).part s+b-a*((lamps).log x U).part s
  calc
    _ = a*(((lamps).log x U).part s+(P.output.old.log x U).part s)+b-a*((lamps).log x U).part s := by ring
    _ = _ := congrArg (fun z : ℂ=>a*z+b-a*((lamps).log x U).part s) join.symm

end YM.Integration.WilsonOlderSignedOneMarkStep
