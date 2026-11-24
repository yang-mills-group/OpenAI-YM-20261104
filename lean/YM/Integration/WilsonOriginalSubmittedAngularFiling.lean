import YM.Integration.WilsonOriginalSubmittedCoverCourse
import YM.Integration.WilsonOriginalRetainedForestFiling

/-! The actual signed re-entry on an independently submitted roster and the complete finite Wick contraction of its two-block public output. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSubmittedAngularFiling
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


def program {G:Gauge}{V ι X:Type}[Fintype V][DecidableEq V](R:Run G){N per j:ℕ}
    (live:j+1<N){o:Passport (R.family.side ((j+1)+1) per) V}
    (rows:ι→Row o (Stock.census V) G X)(grades:V→ℕ)(x:X)(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
    (zero:Γ (j+1) 0=0)(depth order:ℕ):WilsonOriginalCopiedHistory.Values G (Stock.census V) (R.family.side j per):=
  block R (Nat.lt_trans (Nat.lt_succ_self j) live) order
    (receive (block R live order (WilsonOriginalSubmittedCoverCourse.submitted rows grades x
      (π ((j+1)+1)) (AllOrder.Floe.Step.tape depth))) (π (j+1)) (AllOrder.Floe.Step.tape depth)
      grades (Γ (j+1)) zero depth order)

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



variable (sized:shelf ≤ R.alloy.B.a.clock.J j)
local notation "dated" => program R cut M grades x π Γ origin depth order
local notation "actualZero" => Oak.grade0 R hk D Q π Γ floor L.lesson
local notation "nextStamp" => Mutation.stamp lowerStudent (Γ j) actualZero depth order

include file course cut pass month fits narrow x placed names same sized in
theorem original {grid:Side}(div:(R.family.side j per).val∣grid.val)(r:ℕ)(through:r≤order):
    HEq L.input inherited ∧ HEq L.input.hard P.output.hard ∧
    WilsonOriginalRetainedForestFiling.Reads R hk D Q π Γ books floor L.op L.lesson ahead actors
      L.model grades order L.voter x div r ((dated) grid div) ∧
    ∀(s:Multi.Hot (Stock.census V))(e:ℕ),e≤r → ∀y:Stationary.Link G grid,
      (peek div nextStamp grades (π j) tape₀ x e y).part s.val =
        Adjacent.born (fun d z=>((dated) grid div d z).part s.val)
          ((Rebirth.caliber (Γ j) actualZero).back depth) 0 r e y := by
  have earned:∀d≤r,∀y,((dated) grid div d y)=peek div lowerStudent grades (π (j+1)) tape₀ x d y:=
    fun d hd y=>WilsonOriginalSubmittedCoverCourse.original R hk D Q π Γ Ψ books ahead actors pieces
      grades order shelf seats floor physical P L file course cut pass month fits narrow x passport M
      placed names same grid div d (hd.trans through) y
  refine ⟨file.income,file.hard,?_,?_⟩
  · exact WilsonOriginalRetainedForestFiling.original (R:=R) (hk:=hk) (course:=course) (cut:=nextCut)
      (pass:=pass) (month:=month) (fits:=fits) (narrow:=sized) (issued:=L.issued.earning)
      (x:=x) (h:=div) (small:=through) (value:=(dated) grid div) (source:=earned)
  · intro s e he y
    exact WilsonOriginalRetainedStamp.original (R:=R) (hk:=hk) (course:=course) (cut:=nextCut)
      (pass:=pass) (month:=month) (fits:=fits) (narrow:=sized) (issued:=L.issued.earning)
      (x:=x) (h:=div) (small:=through) (kept:=he) (s:=s) (z:=y) (value:=(dated) grid div) (source:=earned)

end YM.Integration.WilsonOriginalSubmittedAngularFiling
