import YM.Integration.WilsonOriginalReceivedFiniteChain
import YM.Integration.WilsonOriginalMeasuredCopiedReset
import YM.Integration.WilsonOriginalReceivedCopiedCover

/-! The whole independently funded copied response and the measured reset on consecutive original Wilson dates. -/
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
open FVA1Physical.TwoReset
open scoped Classical BigOperators


theorem sameCopy {G : Gauge} {n f : Side} {V W I J : Type} [Fintype V] [DecidableEq V]
    {r : Census V} {pa pb : Earn.Passport n V} (a : I → Row pa r G W) (b : J → Row pb r G W)
    (p : pa=pb) (names : I=J) (table : HEq a b) (x : W) (grades : V → ℕ)
    (π : Layout G) (tape : Finset Age) (h : n.val ∣ f.val) :
    copyColor h a grades (fun i=>(a i).paint x) π tape =
    copyColor h b grades (fun i=>(b i).paint x) π tape := by
  subst pb
  subst J
  cases eq_of_heq table
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
/-- At every copied period, the retained earlier model is exactly the reversion of the upper independently published jet. -/
theorem copied_step {grid : Side} (h : (R.family.side (j+1) per).val ∣ grid.val)
    (angle : Stationary.Link G grid) (d : ℕ) (hd : d ≤ order) (face : (Stock.census V).Mode) :
    copyColor h L.model grades (fun i=>(L.model i).paint x) (π (j+1)) tape₀ =
      copyColor h (recorded) grades (fun i=>((recorded) i).paint x) (π (j+1)) tape₀ ∧
    (peek h L.model grades (π (j+1)) tape₀ x d angle).part face =
      Adjacent.born (fun e u=>(peek h (stud) grades (π (j+1)) tape₀ x e u).part face)
        back 0 order d angle := by
  have receiving := sameCopy L.model (recorded) file.passport file.names file.model x grades (π (j+1)) tape₀ h
  have shift := WilsonOriginalMeasuredCopiedReset.original R hk D Q π Γ Ψ course books hi cut P.op P.lesson ahead
    actors P.model P.w grades order shelf P.voter pass month fits narrow _ P.issued.earning x h angle d hd face
  refine ⟨receiving, ?_⟩
  change (Air.discharge _ d (Stationary.arm G _ 1 angle)).part face = _
  rw [receiving]
  exact shift

end YM.Integration.WilsonOriginalReceivedChain
