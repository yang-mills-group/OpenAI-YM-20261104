import YM.Integration.WilsonOriginalThreeFiledModes
import YM.Integration.WilsonOriginalReceivedProgram
import YM.Integration.WilsonReceivedCloseHistory

/-! Two consecutive transfers of a single occupied three-name Wilson experiment. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCarriedThreeStep
open WilsonOriginalReceivedChain WilsonOriginalCopiedHistory
open Extra.Histories MergeProof.Accent Pert.Asymptotics
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Stationary Comparison.RG02 Comparison.RG02.Order Further.PhysicalPeriodLimitF933 Laurent
open FVA1Physical.TwoReset
open scoped Classical BigOperators Topology


variable {G : Gauge} (R : Run G) {m j N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {X : Fin 3 → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : Fin 3 → ℕ)
  (order shelf seats : ℕ) (floor : m ≤ j)
  (physical : Wallet actors → Config G (R.family.side ((j+1)+1) per) → Poly (Stock.census (Fin 3)))

  (P : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1)
    (floor.trans (Nat.le_succ j)) physical)

local notation "earlier" => (fun x : Wallet actors => LocalComparison.actualPush R.family N per (j+1) (physical x))
local notation "elected" => Oak.expenseReal R hk D Q π Γ books (floor.trans (Nat.le_succ j)) P.op P.lesson ahead order shelf
local notation "g" => Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta

local notation "stud" => Oak.student (n:=per) R hk D Q π Γ books (floor.trans (Nat.le_succ j)) P.op P.lesson ahead actors P.model order P.voter
local notation "origin" => Oak.grade0 R hk D Q π Γ (floor.trans (Nat.le_succ j)) P.lesson
local notation "recorded" => Mutation.stamp stud (Γ (j+1)) origin (Burn.horizon k+2) order
local notation "inherited" => Mutation.grow stud (Γ (j+1)) origin (Burn.horizon k+2) order
  (Coat.gStep (Ψ ((j+1)+1)).beta) (Coat.gStep (Ψ (j+1)).beta) (Ψ (j+1)) P.output

variable (L : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats j floor
  (fun x : Wallet actors => LocalComparison.actualPush R.family N per (j+1) (physical x)))
  (file : Filed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P L)
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (cut : j+1 < N)
  (pass : Pass D Q R.alloy R.kit) (month : Scholar.Month R.rolls D Q R.alloy.delay)
  (fits : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J (j+1)) (x : Wallet actors)

local notation "hi" => (floor.trans (Nat.le_succ j))
local notation "depth" => (Burn.horizon k+2)
local notation "tape₀" => AllOrder.Floe.Step.tape depth

local notation "marks" => WilsonSeparatedOriginalJointLog.three
local notation "val₁" => Values G marks (R.family.side (j+1) per)
local notation "nextCut" => Nat.lt_trans (Nat.lt_succ_self j) cut
local notation "lower" => Oak.student (n:=per) R hk D Q π Γ books floor L.op L.lesson ahead actors L.model order L.voter
local notation "nextValue" input:max => block R nextCut order (receive input (π (j+1)) tape₀ grades (Γ (j+1)) origin depth order)
local notation "after" => (fun t : Wallet actors => LocalComparison.actualPush R.family N per j ((earlier) t))
local notation "paidReport" => (Tint.Patrol.report lower L.output (Coat.gStep (Ψ (j+1)).beta)).density

def FiledRead (prior : Wallet actors → val₁) : Prop :=
  WilsonOriginalThreeFiledModes.Read R hk D Q π Γ Ψ books hi cut ahead actors pieces grades order shelf seats physical P prior ∧
  WilsonOriginalThreeFiledModes.Read R hk D Q π Γ Ψ books floor nextCut ahead actors pieces grades order shelf seats earlier L
    (fun t=>nextValue (prior t)) ∧
  (∀ t : Wallet actors, (earlier) t =
    (Tint.Patrol.report stud P.output (Coat.gStep (Ψ ((j+1)+1)).beta)).density t) ∧
  (∀ t : Wallet actors, (after) t=(paidReport) t) ∧
  ∀ (t : Wallet actors) (a : ℕ) (aj : a≤j),
    gust R.family.path N per j ((paidReport) t) a aj = gust R.family.path N per j ((after) t) a aj

include file course pass month fits narrow in
theorem original (prior : Wallet actors → val₁)
    (known : ∀ (t : Wallet actors) (grid : Side) (multiple : (R.family.side (j+1) per).val∣grid.val)
      (d : ℕ), d≤order → ∀ z, prior t grid multiple d z = peek multiple stud grades (π ((j+1)+1)) tape₀ t d z) :
    FiledRead R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P L cut prior := by
  have one := WilsonOriginalThreeFiledModes.original (R:=R) (P:=P) (course:=course) (cut:=cut)
    (named:=prior) (issued:=known)
  have next := WilsonOriginalThreeFiledModes.original (R:=R) (P:=L) (course:=course) (cut:=nextCut)
    (named:=fun t=>nextValue (prior t)) (issued:=fun t grid multiple d small z =>
      WilsonOriginalReceivedProgram.successor (R:=R) (P:=P) (L:=L) (file:=file) (course:=course) (cut:=cut)
        (pass:=pass) (month:=month) (fits:=fits) (narrow:=narrow) (x:=t) (prior:=prior t) (starts:=origin)
        (known:=known t) (grid:=grid) (multiple:=multiple) (d:=d) (hd:=small) (A₀:=z))
  refine ⟨one,next,fun t=>WilsonOriginalReceivedChain.report (R:=R) (P:=P) (x:=t),
    fun t=>WilsonOriginalReceivedChain.report (R:=R) (P:=L) (x:=t),?_⟩
  intro t a aj
  exact congrArg (fun Y=>gust R.family.path N per j Y a aj) (WilsonOriginalReceivedChain.report (R:=R) (P:=L) (x:=t)).symm

end YM.Integration.WilsonOriginalCarriedThreeStep
