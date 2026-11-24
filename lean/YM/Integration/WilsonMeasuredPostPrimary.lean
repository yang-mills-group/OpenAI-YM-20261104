import YM.Integration.WilsonMeasuredFullPrimary
import YM.Integration.WilsonReceivedInheritedFee
import YM.Integration.WilsonOriginalReceivedPost
import YM.Integration.WilsonCenteredSingletonMass

/-! The signed primary of the true Wilson push minus its published group-field
model at a nonbare measured step. The complete original marked gas is retained
in the fieldwise subtraction. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPostPrimary
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph RG16.Guarding
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
theorem original [Nonempty V] (simple:G.Simple) {d:ℕ} (gate:Opened R.family d i per)
    (p:ℕ) (deep:2*(p+1)+8 ≤ order) (aged:p+4 ≤ 3*k+2)
    {ε:ℝ} (ep:0<ε)
    (late:WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged ep ≤ i)
    (x:Wallet actors) (v:V) (root:homes v=0) :
    let C:=R.family
    let W:=Ψ i
    let sec:=C.localSection d
    let w:=Next.Foundations.price G (max W.p.order W.p.power)
    let regular:=(8*Ω^P.op.count)*P.rent+ε*gf^p
    let r:=4*regular
    let s:=(Push.Local.factor C.params sec W.p.supportExponent w*(W.p.order.factorial:ℝ))*r
    let c:=(W.p.order.factorial:ℝ)*r+s+P.w v*W.p.mass (sec.footprint (0:Site (C.side i per))) (w*(s/P.w v))
    let price:=2*max (c/P.w v) (2*(r+s)/P.w v)
    let name:=(Stock.census V).fire v
    let error:=fun U=>(LocalComparison.actualPush C N per i (physical x) U).part name-
      (W.eval U:ℂ)*((lamps).log x U).part name
    ∃ q:store C d per i,reads (C:=C) d N per i q (c/P.w v) ∧ q.forced=0 ∧
      (∀ U, error U=((debt).density x U).part name) ∧
      error =ᶠ[𝓝 1] value (C:=C) d N per i q ∧
      (C.labels.level d).coeffSize (page (C:=C) d per i q) ≤ price ∧
      ∀ f u a,Ink C N per d i f u a → f =ᶠ[𝓝 1] error → u=page (C:=C) d per i q := by
  intro C W sec w regular r s c price name error
  letI:=P.outputCount
  letI:Nonempty (Wallet actors):=⟨x⟩
  have hp:=P.issued.earning.positive
  have inc:=WilsonReceivedInheritedFee.original R hk D Q π Γ Ψ books hi cut P.op P.lesson ahead actors P.model
    P.w grades order shelf P.voter P.cost pieces P.input P.rent P.output P.issued simple p deep aged ep late
  have reg:P.output.old.Paid P.w W.p.B (W.p.supportExponent+2) regular := by
    simpa only [add_assoc,one_add_one_eq_two] using P.output.old.loan_monotone P.issued.tuition inc
  have actual:=(course.1.walk i hi cut.le).truep
  obtain ⟨q,paid,blank,charged,priced,heard⟩:=WilsonMeasuredFullPrimary.original R π Γ Ψ course hi cut.le gate
    debt hp actual.valid.labels.forced reg P.issued.paidForce x v root
  have same (U:Config G (C.side i per)) : error U=((debt).density x U).part name := by
    have aw:=QuadraticLocal.Earn.Scene.Armada.paid student P.w grades P.issued.earning W.p P.issued.Waffle.soon
    have win:0≤width:=by linarith only [W.p.exponent_pos]
    have hs:=aw.sums win hp x U
    have hr:=P.issued.tuition.sums win hp x U
    have hj:=(Lamps.joinPaid aw P.issued.tuition).sums win hp x U
    have hd:=Hard.packet_summing P.output.hard P.issued.paidForce W.p.exponent_pos.le hp x U
    have report:=congrFun (WilsonOriginalReceivedChain.report R hk D Q π Γ Ψ books ahead actors pieces grades
      order shelf seats i hi physical P x) U
    change (LocalComparison.actualPush C N per i (physical x) U).part name-
      (W.eval U:ℂ)*((lamps).log x U).part name=((debt).density x U).part name
    rw [report, WilsonCenteredSingletonMass.ordinary debt x U v hr hd,
        WilsonCenteredSingletonMass.ordinary gauge x U v hj hd]
    have joined:((gauge).E.log x U).part name=((lamps).log x U).part name+(P.output.old.log x U).part name:=
      congrArg (fun z:Poly (Stock.census V)=>z.part name) (Lamps.joinLog x U hs hr)
    let a:ℂ:=W.eval U
    let b:ℂ:=(Real.exp (W.exponent U):ℂ)*((debt).gas x U).part name
    change a*((gauge).E.log x U).part name+b-a*((lamps).log x U).part name =
      a*(P.output.old.log x U).part name+b
    rw [joined]
    ring
  have eg: error =ᶠ[𝓝 1] (fun U=>((debt).density x U).part name):=EventuallyEq.of_eq (funext same)
  exact ⟨q,paid,blank,same,eg.trans charged,priced,fun f u a ink germ=>heard f u a ink (germ.trans eg)⟩

end YM.Integration.WilsonMeasuredPostPrimary
end

