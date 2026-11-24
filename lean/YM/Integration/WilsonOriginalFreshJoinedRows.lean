import YM.Integration.WilsonOriginalOccupiedFiledSlice
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFreshJoinedRows
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


include cut in
theorem earned (simple:G.Simple)(way:WayStation R.kit)(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (pole p:ℕ)(sourced:∀t:(marks).Mode,(∑v∈t.val,grades v)+1 ≤ pole)
    (hardFloor:6*seats ≤ R.alloy.B.a.clock.J i)(deep:2*(p+1)+8 ≤ order)(aged:p+4 ≤ 3*k+2)
    {ε:ℝ}(ep:0<ε)(opened:WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged ep ≤ i) (x:Wallet actors):
    let debt:=(8*Ω^P.op.count)*P.rent+ε*g^p
    (lamps).Paid P.w (Ψ i).p.B ((Ψ i).p.supportExponent+2) cash ∧
      P.output.old.Paid P.w (Ψ i).p.B ((Ψ i).p.supportExponent+2) debt ∧
      (∀U,Summable (fun j=>(lamps).frame j x U)) ∧
      (∀U,Summable (fun j=>P.output.old.frame j x U)) ∧
      ∀U,((lamps).join P.output.old).log x U=(lamps).log x U+P.output.old.log x U:=by
  intro debt
  obtain ⟨soft,_,old,_,_⟩:=WilsonOriginalFiledSuccessorIncome.original R hk D Q π Γ Ψ books hi cut ahead
    actors pieces grades order shelf seats physical P simple way course pole p sourced hardFloor deep aged ep opened
  have positive:0 ≤ (Ψ i).p.supportExponent+2:=by linarith only [(Ψ i).p.exponent_pos]
  have L:=soft.sums positive P.issued.earning.positive x
  have O:=old.sums positive P.issued.earning.positive x
  exact ⟨soft,old,L,O,fun U=>Lamps.joinLog x U (L U) (O U)⟩

theorem bare {G:Gauge}{n:Side}{V X I:Type}[DecidableEq V]{J:Census V}{o:Earn.Passport n V}
    (M:I→Earn.Row o J G X)(b:BudgetPoint)(y:ℝ)(x:X)(U:Config G n):
    WilsonRootedKioskOccupiedSlip.bare (rendered M b y) x U=Spill.Foundry.uncut M y x U:=rfl

theorem posted {G:Gauge}{n:Side}{V X I T:Type}[Fintype V][DecidableEq V][Fintype T]
    {J:Census V}{o:Earn.Passport n V} (M:I→Earn.Row o J G X)(b:BudgetPoint)(y:ℝ)
    (D:Config G n→ℝ)(tag:T→J.Mode)(live:∀j,(tag j).val.Nonempty)
    (z:T → X → Config G n → ℂ)
    (declared:∀x U,Spill.Foundry.uncut M y x U=∑j,Poly.send (tag j) (z j x U))
    (x:X)(U:Config G n):
    (D U:ℂ) • ∏j,(1+Poly.send (tag j) (z j x U))=
    (D U:ℂ) • Poly.pass (WilsonRootedKioskOccupiedSlip.bare (rendered M b y) x U):=by
  rw [WilsonOriginalFreshJoinedRows.bare,declared,Extra.Trajectories.pass_sum univ tag (fun j _=>live j)]

end YM.Integration.WilsonOriginalFreshJoinedRows
end
