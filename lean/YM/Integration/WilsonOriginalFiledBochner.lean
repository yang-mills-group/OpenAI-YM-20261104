import YM.Integration.WilsonOriginalOrdinaryBochner
import YM.Integration.WilsonOriginalFiledSuccessorIncome

/-! Integrability on the dated Wilson course at the submitted source weights. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFiledBochner
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

open MeasureTheory WilsonRootedKioskOccupiedSlip

theorem envelope {G:Gauge} (R:Run G) {N per m k i:ℕ} {π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    {Ψ:∀j,RG.Rep G (R.family.side j per)} (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (lo:m ≤ i)(hi:i ≤ N):Envelope (Ψ i).eval:=by
  have same:(Ψ i).eval=(R.family.path.rep N per i).eval:=(course.1.walk i lo hi).view
  exact same.symm ▸ (R.family.path.rep N per i).envelope (R.makes.wilson.represents N per i hi).good

theorem original {G:Gauge} (R:Run G) {N per m k i:ℕ} {π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    {Ψ:∀j,RG.Rep G (R.family.side j per)} (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (lo:m ≤ i)(hi:i ≤ N)
    {V X X' ι μ ι':Type}[Fintype V][DecidableEq V][Countable ι][Countable μ][Countable ι']
    {J:Census V}{o o':V→Site (R.family.side i per)}{p':BudgetPoint}
    (L:Lamps X ι G (Ψ i).p o J)(old:Lamps X μ G (Ψ i).p o J)(next:Lamps X' ι' G p' o' J)
    {w w':V→ℝ}(hw:∀v,0<w v)(hw':∀v,0<w' v){a a' E C rent:ℝ}
    (width:0 ≤ a)(width':0 ≤ a')(paid:L.Paid w (Ψ i).p.B a E)(refund:old.Paid w (Ψ i).p.B a rent)
    (stock:Gross next w' p'.B a' C)(x:X)(z:X'):
    Integrable (fun U=>((Ψ i).eval U:ℂ) • Poly.pass ((L.join old).log x U)) (prior G _) ∧
    Integrable (fun U=>((Ψ i).eval U:ℂ) • Poly.pass (bare next z U)) (prior G _):=by
  have quiet:=envelope R course lo hi
  exact ⟨WilsonOriginalOrdinaryBochner.regular (Ψ i) quiet (L.join old) hw width (Lamps.joinPaid paid refund) x,
    WilsonOriginalOrdinaryBochner.unmasked (Ψ i) quiet next hw' width' stock z⟩

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m  ≤  i) (cut : i < N)
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
local notation "g" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "lamps" => rendered student (Ψ i).p oldG
local notation "gauge" => Tint.Patrol.report student P.output oldG
local notation "width" => ((Ψ i).p.supportExponent+1+1)
local notation "cash" => Invoice.price (Ψ i).p (fig).mist (order+shelf+1) P.op.count width (fig).limitC G*
  ((fig).produce (sheet).ratio.count*P.cost)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "marks" => Stock.census V

open WilsonRootedKioskOccupiedSlip WilsonOriginalFlatFiledMask

include cut in
theorem successor (simple:G.Simple)(way:WayStation R.kit)(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (pole p:ℕ)(sourced:∀t:(marks).Mode,(∑v∈t.val,grades v)+1 ≤ pole)
    (hardFloor:6*seats ≤ R.alloy.B.a.clock.J i)(deep:2*(p+1)+8 ≤ order)(aged:p+4 ≤ 3*k+2)
    {ε:ℝ}(ep:0<ε)(opened:WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged ep ≤ i):

    ∀x:Wallet actors,
      Integrable (fun U=>((Ψ i).eval U:ℂ) • Poly.pass (((lamps).join P.output.old).log x U)) (prior G _) ∧
      Integrable (fun U=>((Ψ i).eval U:ℂ) • Poly.pass (bare (lamps) x U)) (prior G _):=by
  intro x
  letI:Countable P.modelIndex:=P.modelCount
  letI:Countable P.outputIndex:=P.outputCount
  let siz:=(R.alloy.B.a.S.oneStep i per).exact_size
  let epoch:=Oak.era R hk D Q π Γ hi P.op P.lesson
  let text:=Cruise.publish D R.rolls Q R.alloy φ books P.op epoch siz P.model order P.voter P.lesson.entry
  letI students:Countable (Scene.Texts P.model (Pane.panel R.alloy i siz).ratio text):=
    Scene.crewC P.model _ text (Cruise.funded D R.rolls Q R.alloy φ books P.op epoch siz P.model
      order P.voter P.lesson.entry P.lesson.studied ahead)
  obtain ⟨soft,raw,old,_⟩:=WilsonOriginalFiledSuccessorIncome.original R hk D Q π Γ Ψ books
    hi cut ahead actors pieces grades order shelf seats physical P simple way course pole p sourced
    hardFloor deep aged ep opened
  have width':0 ≤ (Ψ i).p.supportExponent+2:=by linarith only [(Ψ i).p.exponent_pos]
  exact original R course hi cut.le (ι:=Scene.Texts P.model (Pane.panel R.alloy i siz).ratio text)
    (ι':=Scene.Texts P.model (Pane.panel R.alloy i siz).ratio text) (μ:=P.outputIndex)
    (lamps) P.output.old (lamps) P.issued.earning.positive
    P.issued.earning.positive width' width' soft old raw x x

end YM.Integration.WilsonOriginalFiledBochner
end
