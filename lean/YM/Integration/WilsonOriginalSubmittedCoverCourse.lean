import YM.Integration.WilsonOriginalReceivedProgram
import YM.Integration.WilsonOriginalFiledCopiedStep

/-! Two original covered blocks of an independently submitted marked roster, on the same
dated post and its real filed successor. Both vacua and the intervening kinetic reset are retained. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSubmittedCoverCourse
open WilsonOriginalReceivedChain WilsonOriginalCopiedHistory
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Stationary Comparison.RG02 Comparison.RG02.Order Further.PhysicalPeriodLimitF933 Laurent
open FVA1Physical.TwoReset
open scoped Classical BigOperators Topology


def submitted {G:Gauge}{n:Side}{V ι X:Type}[Fintype V][DecidableEq V]{o:Passport n V}
    {C:Census V}(rows:ι→Row o C G X)(weights:V→ℕ)(test:X)(layout:Layout G)(tape:Finset Age):
    WilsonOriginalCopiedHistory.Colors G C n :=
  fun _ div=>copyColor div rows weights (fun v=>(rows v).paint test) layout tape

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



local notation "nextCut" => Nat.lt_trans (Nat.lt_succ_self j) cut
local notation "lowerStudent" => Oak.student (n:=per) R hk D Q π Γ books floor L.op L.lesson ahead actors
  L.model order L.voter
local notation "C₀" => Stock.census V
local notation "date" => R.family.side (j+1) per


variable {ι:Type}(passport:Passport (R.family.side ((j+1)+1) per) V)
  (M:ι→Row passport (Stock.census V) G (Wallet actors))
  (placed:P.passport=passport)(names:P.modelIndex=ι)(same:HEq P.model M)


include course cut x placed names same in
theorem upper (grid:Side)(div:(date).val∣grid.val)(e:ℕ)(_kept:e≤order)(A:Stationary.Link G grid):
    (WilsonOriginalCopiedHistory.block R cut order (submitted M grades x (π ((j+1)+1)) tape₀)) grid div e A=peek div stud grades (π ((j+1)+1)) tape₀ x e A:=by
  have born:=WilsonOriginalReceivedCopiedCover.published R hk D Q π Γ Ψ course books hi cut ahead actors
    pieces grades order shelf seats physical P
  apply WilsonOriginalCoverCoefficient.identified
  apply WilsonOriginalCopiedContraction.named (h:=cut) (p:=order) (M:=P.model) (Y:=stud)
    (published:=born) (t:=x) (grid:=grid) (multiple:=div) (e:=e) (he:=_kept)
  intro c
  exact WilsonOriginalReceivedChain.sameCopy P.model M placed names same x grades (π ((j+1)+1)) tape₀
    (tiled R div c)

include file course cut pass month fits narrow x placed names same in
theorem original (grid:Side)(div:(R.family.side j per).val∣grid.val)(e:ℕ)(_kept:e≤order)
    (A:Stationary.Link G grid):
    WilsonOriginalCopiedHistory.block R nextCut order
      (WilsonOriginalCopiedHistory.receive (WilsonOriginalCopiedHistory.block R cut order (submitted M grades x (π ((j+1)+1)) tape₀)) (π (j+1)) tape₀ grades (Γ (j+1)) origin depth order)
      grid div e A=peek div lowerStudent grades (π (j+1)) tape₀ x e A:=by
  apply WilsonOriginalReceivedProgram.successor (R:=R) (hk:=hk) (P:=P) (L:=L) (file:=file)
    (course:=course) (cut:=cut) (pass:=pass) (month:=month) (fits:=fits) (narrow:=narrow)
    (x:=x) (prior:=WilsonOriginalCopiedHistory.block R cut order (submitted M grades x (π ((j+1)+1)) tape₀)) (starts:=origin) (grid:=grid) (multiple:=div) (d:=e) (hd:=_kept)
  exact fun grid div a bound A=>upper R hk D Q π Γ Ψ books ahead actors pieces grades order shelf
    seats floor physical P course cut x passport M placed names same grid div a bound A

end YM.Integration.WilsonOriginalSubmittedCoverCourse
