import YM.Integration.WilsonOriginalReceivedFiledChain
import YM.Integration.WilsonOriginalMeasuredStampCoefficients

/-! The independently filed finite marked bank across an actual received date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalReceivedChain
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Stationary Comparison.RG02 Comparison.RG02.Order Further.PhysicalPeriodLimitF933 Laurent
open scoped Classical BigOperators

private theorem sameBank {G : Gauge} {n : Side} {V W I J : Type} [Fintype V] [DecidableEq V]
    {r : Census V} {pa pb : Earn.Passport n V} (a : I → Row pa r G W) (b : J → Row pb r G W)
    (p : pa=pb) (names : I=J) (model : HEq a b) (x : W) (grades : V → ℕ) (π : Layout G) (d : ℕ) :
    Air.craft a (fun i=>(a i).paint x) grades π (AllOrder.Floe.Step.tape d) =
      Air.craft b (fun i=>(b i).paint x) grades π (AllOrder.Floe.Step.tape d) := by
  subst pb
  subst J
  cases eq_of_heq model
  rfl

variable {G : Gauge} (R : Run G) {m j N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (floor : m ≤ j)
  (physical : Wallet actors → Config G (R.family.side ((j+1)+1) per) → Poly (Stock.census V))

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
local notation "bankNow" => Air.craft L.model (fun v=>(L.model v).paint x) grades (π (j+1)) tape₀
local notation "priorBank" => Air.craft P.model (fun v=>(P.model v).paint x) grades (π ((j+1)+1)) tape₀
local notation "upperBank" => Air.craft stud (fun v=>((stud) v).paint x) grades (π (j+1)) tape₀
local notation "stampedBank" => Air.craft recorded (fun v=>((recorded) v).paint x) grades (π (j+1)) tape₀
local notation "arm" => Stationary.arm G (R.family.side (j+1) per) 1
local notation "curriculum" => litP D R.alloy Q (hk.trans (R.alloy.B.a.fits.mono hi)) P.lesson.entry
local notation "back" => ((Rebirth.caliber ((curriculum).issue P.lesson.entry) ((curriculum).sustenance.due P.lesson.entry).1).back depth)

include file course cut pass month fits narrow in
/-- All occupied modes on the actual earlier port use the same measured change of coupling. -/
theorem reset_bank :
    bankNow = stampedBank ∧
    ∀ (A : Stationary.Link G (R.family.side (j+1) per)) r, r ≤ order →
      ∀ s : (Stock.census V).Mode, (Air.discharge bankNow r (arm A)).part s =
        Adjacent.born (fun e a=>(Air.discharge upperBank e (arm a)).part s) back 0 order r A := by
  have eqn := sameBank L.model (recorded) file.passport file.names file.model x grades (π (j+1)) depth
  have stamp := WilsonOriginalMeasuredStampCoefficients.original R hk D Q π Γ Ψ course books hi cut P.op P.lesson ahead
    actors P.model P.w grades order shelf P.voter pass month fits narrow _ P.issued.earning x
  exact ⟨eqn, fun A r hr s => (congrArg (fun u => (Air.discharge u r (arm A)).part s) eqn).trans (stamp.2.2 A r hr s)⟩

include file course cut pass month fits narrow in
/-- At a fixed order the genuine finite Gaussian coefficient is the unreset row plus
its funded signed winding term. The row at the next date is its measured reversion. -/
theorem finite_step (F : Forest (R.family.path.levels.clock.op (j+1) per).ratio)
    (tag : (R.family.path.levels.clock.op (j+1) per).Choices)
    (A : Stationary.Link G (R.family.side (j+1) per)) (r : ℕ) (hr : r ≤ order) :
    ∃ e : Poly (Stock.census V),
      Order.observe (Stock.census V) order (Order.logMarked (PhysicalWilsonPeriodizedMaterial.reference R N (j+1)
        per cut (arm A) priorBank order)) r = Air.discharge upperBank r (arm A)+e ∧
      Poly.price P.w e ≤ Oak.Tutoring.bill R hk D Q π Γ books hi P.op P.lesson A P.cost ∧
      ∀ s : (Stock.census V).Mode, (Air.discharge bankNow r (arm A)).part s =
        Adjacent.born (fun e a=>(Air.discharge upperBank e (arm a)).part s) back 0 order r A := by
  have ref := WilsonOriginalRosterFiniteMaterial.original R hk D Q π Γ Ψ course books hi cut P.op P.lesson ahead actors P.model
    P.w grades order shelf P.voter P.cost P.salary x F tag A _ P.issued.earning
    (P.affordable.trans (inv_le_one_of_one_le₀ P.issued.Waffle.cool))
  obtain ⟨e,exactRead,rate,_,_⟩ := ref.2.2 r hr
  have regular := reset_bank R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P L file course cut pass month fits narrow x
  exact ⟨e,exactRead,rate,regular.2 A r hr⟩

end YM.Integration.WilsonOriginalReceivedChain
