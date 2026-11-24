import YM.Integration.WilsonMeasuredPostPrimary
import YM.Integration.WilsonOlderFreshIssuedIntake
import YM.Integration.WilsonMeasuredRankedGerm

/-! At every protected held field, the whole original one-step signed
numerator reads the actual unmasked student plus its genuine old regular row. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredRankedLights
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

theorem unmasked {G:Gauge} {n:Side} {p:BudgetPoint} {V T I:Type}
    [DecidableEq V] {o:V→Site n} {c:Census V} (L:Lamps T I G p o c)
    (x:T) (U:Config G n) (clear:flags p.threshold U=∅) :
    L.log x U=WilsonRootedKioskOccupiedSlip.bare L x U := by
  apply tsum_congr
  intro j
  have ok:Healthy p.threshold (L.ground j) U:=by simp [Healthy,clear]
  have lit:L.light x j U=L.nominal x j U:=by
    rw [Lamps.light]
    split
    · rfl
    · exact masked_eq _ _ _ _ ok
  exact congrArg (Poly.send (L.mode j)) lit

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


theorem original [Nonempty V] (x:Wallet actors) (v:V) (U:Config G (R.family.side i per))
    (clear:flags (Ψ i).p.threshold U=∅) :
    (LocalComparison.actualPush R.family N per i (physical x) U).part ((Stock.census V).fire v) =
      ((Ψ i).eval U:ℂ)*((Spill.Foundry.uncut student oldG x U).part ((Stock.census V).fire v)+
        (P.output.old.log x U).part ((Stock.census V).fire v)) := by
  letI:=P.outputCount
  letI:Nonempty (Wallet actors):=⟨x⟩
  have hp:=P.issued.earning.positive
  let W:=Ψ i
  have aw:=QuadraticLocal.Earn.Scene.Armada.paid student P.w grades P.issued.earning W.p P.issued.Waffle.soon
  have win:0≤width:=by linarith only [W.p.exponent_pos]
  have hs:=aw.sums win hp x U
  have hr:=P.issued.tuition.sums win hp x U
  have paid:=(Lamps.joinPaid aw P.issued.tuition)
  have widthEq:width=W.p.supportExponent+2:=by ring
  rw [widthEq] at paid
  have whole:=WilsonMeasuredFullPrimary.healthy gauge hp paid x v U clear
  have report:=congrFun (WilsonOriginalReceivedChain.report R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical P x) U
  rw [report,whole]
  have joined:=Lamps.joinLog (L:=lamps) (A:=P.output.old) x U hs hr
  have lit:=unmasked lamps x U clear
  change (lamps).log x U=Spill.Foundry.uncut student oldG x U at lit
  exact congrArg (fun z : Poly (Stock.census V) => (W.eval U:ℂ)*z.part ((Stock.census V).fire v))
    (joined.trans (congrArg (·+P.output.old.log x U) lit))

end YM.Integration.WilsonMeasuredRankedLights
