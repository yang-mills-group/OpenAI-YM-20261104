import YM.Integration.WilsonOriginalFlatFiledHearing
import YM.Integration.WilsonReceivedForcedExit
import YM.Integration.WilsonReceivedInheritedFee
import YM.Integration.WilsonMarkedFixedPoleGross
import YM.Integration.WilsonReceivedWholeFieldHot
import YM.Integration.WilsonPhysicalMarkedDefectPrescribedInput

/-! Cash the four accounts of the actually issued successor on its original
test radii. The unmasked Laurent pole is determined by the submitted grades. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFiledSuccessorIncome
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
theorem original (simple:G.Simple)(way:WayStation R.kit)(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (pole p:ℕ)(sourced:∀t:(marks).Mode,(∑v∈t.val,grades v)+1 ≤ pole)
    (hardFloor:6*seats ≤ R.alloy.B.a.clock.J i)(deep:2*(p+1)+8 ≤ order)(aged:p+4 ≤ 3*k+2)
    {ε:ℝ}(ep:0<ε)(opened:WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged ep ≤ i):
    let raw:=((2:ℝ)^(order+shelf+1)/oldG^pole)*cash
    let debt:=(8*Ω^P.op.count)*P.rent+ε*g^p
    (lamps).Paid P.w (Ψ i).p.B ((Ψ i).p.supportExponent+2) cash ∧
      Gross (lamps) P.w (Ψ i).p.B ((Ψ i).p.supportExponent+2) raw ∧
      P.output.old.Paid P.w (Ψ i).p.B ((Ψ i).p.supportExponent+2) debt ∧
      P.output.hard.Paid P.w (Ψ i).p.B (Ψ i).p.supportExponent κ ∧
      ∀x,LocalComparison.actualPush R.family N per i (physical x)=(posted (lamps) P.output.old P.output.hard).density x:=by
  intro raw debt
  have widthEq:width=(Ψ i).p.supportExponent+2:=by ring
  have soft:=Scene.Armada.paid student P.w grades P.issued.earning (Ψ i).p P.issued.Waffle.soon
  have unc:=WilsonMarkedFixedPoleGross.landed student P.w grades (Ψ i).p P.issued.earning P.issued.Waffle.soon pole sourced
  have oldBound:=WilsonReceivedInheritedFee.original R hk D Q π Γ Ψ books hi cut P.op P.lesson ahead actors P.model
    P.w grades order shelf P.voter P.cost pieces P.input P.rent P.output P.issued simple p deep aged ep opened
  have hard:=WilsonReceivedForcedExit.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
    hi physical P cut way course 0 (by simpa using hardFloor)
  refine ⟨?_,?_,?_,?_,fun x=>WilsonOriginalReceivedChain.report R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical P x⟩
  · rw [←widthEq]
    exact soft
  · rw [←widthEq]
    exact unc
  · rw [←widthEq]
    exact P.output.old.loan_monotone P.issued.tuition oldBound
  · simpa only [Nat.cast_zero,neg_zero,Real.rpow_zero,one_mul] using hard

end YM.Integration.WilsonOriginalFiledSuccessorIncome
