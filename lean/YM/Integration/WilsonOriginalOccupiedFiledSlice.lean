import YM.Integration.WilsonOriginalOccupiedWindow
import YM.Integration.WilsonOriginalJointTrialHearing

/-! Original joint filed edge, its signed marked withdrawal and unchanged full regular log. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedFiledSlice
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

private abbrev rowsOf {G:Gauge} {n:Side} {V X I:Type} [DecidableEq V] {o:V → Site n} {P:BudgetPoint}
    {J:Census V} (_:Lamps X I G P o J):=I

open private YM.Integration.WilsonOriginalOccupiedCorridor.weaker from YM.Integration.WilsonOriginalOccupiedCorridor
include cut in
theorem original (simple:G.Simple)(way:WayStation R.kit)(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (pole p:ℕ)(sourced:∀t:(marks).Mode,(∑v∈t.val,grades v)+1 ≤ pole)
    (hardFloor:6*seats ≤ R.alloy.B.a.clock.J i)(deep:2*(p+1)+8 ≤ order)(aged:p+4 ≤ 3*k+2)
    {ε:ℝ}(ep:0<ε)(opened:WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged ep ≤ i) (x:Wallet actors):
    let debt:=(8*Ω^P.op.count)*P.rent+ε*g^p
    ∃row:WilsonOriginalOccupiedWindow.Slice R marks (Ψ i),
      row.w=P.w ∧ row.regular=cash+debt ∧ row.hard=1 ∧
      row.A.density row.x=LocalComparison.actualPush R.family N per i (physical x) ∧
      (∀U,row.A.E.log row.x U=(lamps).log x U+P.output.old.log x U) ∧
      ∀{b:ℕ},m ≤ b → ∀(bi:b ≤ i) (s:(marks).Mode) (W:Config G (R.family.side b per)),
        WilsonOriginalOccupiedWindow.credit R marks (N:=N) bi Ψ row s W=
          WilsonOriginalJointTrialHearing.read R N per W bi (LocalComparison.actualPush R.family N per i (physical x)) s-
          WilsonOriginalJointTrialHearing.read R N per W bi
            (fun U=>((Ψ i).eval U:ℂ) • Poly.pass ((lamps).log x U+P.output.old.log x U)) s:=by
  intro debt
  letI:Countable P.outputIndex:=P.outputCount
  letI:Countable P.modelIndex:=P.modelCount
  letI:Countable (rowsOf (lamps)):=Scene.crewC P.model _ _ (Cruise.funded D R.rolls Q R.alloy φ books P.op
    (Oak.era R hk D Q π Γ hi P.op P.lesson) (R.alloy.B.a.S.oneStep i per).exact_size P.model
    order P.voter P.lesson.entry P.lesson.studied ahead)
  obtain ⟨soft,_,old,hard,field⟩:=WilsonOriginalFiledSuccessorIncome.original R hk D Q π Γ Ψ books hi cut ahead
    actors pieces grades order shelf seats physical P simple way course pole p sourced hardFloor deep aged ep opened
  let A:=posted (lamps) P.output.old P.output.hard
  have paid:=Lamps.joinPaid soft old
  have combined:A.E.Paid P.w (Ψ i).p.B (Ψ i).p.supportExponent (cash+debt):=
    YM.Integration.WilsonOriginalOccupiedCorridor.weaker A.E _ P.issued.earning.positive paid (by linarith)
  let row:WilsonOriginalOccupiedWindow.Slice R marks (Ψ i):=
    { X:=Wallet actors, I:=(rowsOf (lamps))⊕P.outputIndex, count:=inferInstance, x:=x,
      o:=_, A:=A, w:=P.w, positive:=P.issued.earning.positive, regular:=cash+debt, hard:=1,
      earned:=combined, forced:=by
        change P.output.hard.Paid _ _ _ (1*κ);rw [one_mul];exact hard }
  have all:row.A.density row.x=LocalComparison.actualPush R.family N per i (physical x):=(field x).symm
  have h0:0 ≤ (Ψ i).p.supportExponent+2:=by linarith only [(Ψ i).p.exponent_pos]
  have lamp:∀U,row.A.E.log row.x U=(lamps).log x U+P.output.old.log x U:=fun U=>
    Lamps.joinLog x U (soft.sums h0 P.issued.earning.positive x U) (old.sums h0 P.issued.earning.positive x U)
  refine ⟨row,rfl,rfl,rfl,all,lamp,?_⟩
  intro b mb bi s W
  have quiet:((Ψ b).eval W:ℂ)=((R.family.path.rep N per b).eval W:ℂ):=by
    exact_mod_cast congrFun (course.1.walk b mb (bi.trans cut.le)).view W
  unfold WilsonOriginalOccupiedWindow.credit WilsonOriginalJointTrialHearing.read
  simp only [quiet,all,lamp,mul_sub]

end YM.Integration.WilsonOriginalOccupiedFiledSlice
