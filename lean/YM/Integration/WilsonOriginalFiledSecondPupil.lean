import YM.Integration.WilsonOriginalFiledRetainedForest
import YM.Integration.WilsonOriginalReceivedGradeRestriction
/-! The true second pupil reads the nested covered Gaussian program at any retained order on its own filed model. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFiledSecondPupil
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


include course cut in
theorem original (r:ℕ)(small:r≤order)(prior:WilsonOriginalCopiedHistory.Values G C₀ date)
    (starts:(Γ (j+1)) 0=0)
    (earned:∀(fine:Side)(tiles:(date).val ∣ fine.val),
      WilsonOriginalFiledRetainedForest.Reads R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P L
        x tiles r (prior fine tiles))
    (grid:Side)(multiple:(R.family.side j per).val ∣ grid.val)(d:ℕ)(kept:d≤r)(u:Stationary.Link G grid):
    WilsonOriginalCopiedHistory.block R nextCut r
      (WilsonOriginalCopiedHistory.receive prior (π (j+1)) tape₀ grades (Γ (j+1)) starts depth r)
      grid multiple d u = peek multiple lowerStudent grades (π (j+1)) tape₀ x d u:=by
  let trees:=WilsonOriginalCopiedHistory.forest R j grid
  let tags:=WilsonOriginalCopiedHistory.tag R j grid
  let raw:=fun c:Covers R.family.path.levels.S j grid=>
    copyColor (tiled R multiple c) L.model grades (fun v=>(L.model v).paint x) (π (j+1)) tape₀
  have pub:=WilsonOriginalReceivedCopiedCover.published R hk D Q π Γ Ψ course books floor nextCut ahead
    actors pieces grades order shelf seats earlier L
  have nailed:=WilsonOriginalCopiedContraction.named (R:=R) (h:=nextCut) (p:=order) (M:=L.model)
    (Y:=lowerStudent) (published:=pub) (t:=x) (grid:=grid) (multiple:=multiple) (inputs:=raw)
    (matched:=fun _=>rfl) (F:=trees) (tag:=tags) (A:=u) (e:=d) (he:=kept.trans small)
  apply WilsonOriginalCoverCoefficient.identified
  apply nailed.congr'
  filter_upwards with c
  let fine:=R.family.side (j+1) c.val
  let tiles:=tiled R multiple c
  let K:=(RunFormalChain.fromRun R).step N j c.val nextCut
  let z:=Stationary.arm G (R.family.side j c.val) 1 (AllOrder.Ker.convey (coverWin c.prop) u)
  have joined:=earned fine tiles K (trees c) (tags c) z
  have observed:=WilsonOriginalReceivedGradeRestriction.original K (trees c) (tags c) (raw c) z small d kept
  unfold WilsonOriginalCopiedContraction.contraction
  apply congrArg (fun a:Poly C₀=>(Pages grid (R.family.side j c.val):ℝ)⁻¹ • a)
  exact observed.trans (congrArg (fun u=>Order.observe C₀ r (Order.logMarked u) d) joined)

end YM.Integration.WilsonOriginalFiledSecondPupil
