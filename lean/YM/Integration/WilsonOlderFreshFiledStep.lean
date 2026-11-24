import YM.Integration.WilsonOlderFreshReversionStore
import YM.Integration.WilsonOlderFreshPlant

/-! Replant each independently issued group word directly on its own complete older Wilson vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshFiledStep
open Filter Labels Source Planned.GuardedAtom Push.Local
open WilsonOriginalReceivedChain
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Stationary Comparison.RG02 Comparison.RG02.Order Further.PhysicalPeriodLimitF933 Laurent
open scoped Classical BigOperators

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
local notation "gu" => Coat.gStep (Ψ ((j+1)+1)).beta
local notation "gl" => Coat.gStep (Ψ (j+1)).beta
local notation "older" => R.family.path.rep N per (j+1)
local notation "reverted" => Mutation.mend stud (Ψ (j+1)).p (Γ (j+1)) origin depth order gu gl
local notation "α" => (Ψ (j+1)).p.supportExponent+1+1

local notation "βh" => R.alloy.B.a.clock.hatBeta ((j+1)+1)
local notation "rp" => Ψ (j+1)
local notation "allowance" => R.alloy.B.a.clock.forcedAllowance (j+1)
local notation "κ" => LocalComparison.forcedDivisor R.family (j+1)
local notation "roots" => (P.passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "allFee" => (Spill.allOver (rp).p)^(order+shelf+1)

include course cut pass month fits narrow in
theorem booked (simple : G.Simple) {η ε : ℝ} (positive : 0<η) (unit : η≤1) (ep : 0<ε)
    (opened : WilsonCoherentMayerMutationIntake.firstDate R simple order positive unit ep≤j+1) :
    WilsonRootedKioskOccupiedSlip.Gross reverted P.w (rp).p.B α (allFee*(ε*g^((order:ℝ)+1-η)*P.cost)) := by
  let C:=(R.family.path.levels.clock.op (j+1) per).ratio.count
  have ch:=WilsonOriginalMeasuredReentry.credited R hk D Q pass π Γ Ψ course hi cut P.lesson books P.op
    ahead month order shelf fits narrow
  have cash:=P.issued.Waffle
  have rate:=(eventually_atTop.mp (WilsonCoherentMayerMutationRate.tested R simple order positive unit ep)).choose_spec (j+1) opened
  have grade : (fig).fidelity=βh^Mentor.Tuition.need order (Mentor.Tolerance (R.alloy.B.a.clock.J (j+1))) := by
    rw [PriceCompiler.beta_eq R.alloy.B.valid (j+1)]
    rfl
  have small:=rate N per cut fig C (Ψ ((j+1)+1)).p (rp).p _ _ _ P.cost cash P.issued.Beamwork
    (Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0)) grade
  obtain ⟨f,pos,sup,hit⟩:=(WilsonOlderFreshReversionGross.original stud (rp).p (Γ (j+1)) origin depth order
    gu gl P.w grades ch.1 P.issued.earning cash.soon cash.bloom.le).before
  exact ⟨f,pos,sup,fun y=>Push.AbsoluteSums.budget_loosen (hit y)
    (mul_le_mul_of_nonneg_left small (pow_nonneg (zero_le_one.trans (Spill.allOver_ge _)) _))⟩

include file course cut pass month fits narrow in
theorem balance (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (load : seats≤Burn.horizon k+2) (simple : G.Simple) {η ε : ℝ}
    (positive : 0<η) (unit : η≤1) (ep : 0<ε)
    (opened : WilsonCoherentMayerMutationIntake.firstDate R simple order positive unit ep≤j+1)
    (late : WilsonCenteredCaptureClock.first R simple≤j+1) (v : V)
    (Z : Support (R.family.side (j+1) per)) (y : Site (R.family.side (j+1) per))
    (center : y∈Z) (member : roots v∈Z) (rad : ℕ) (near : separation (roots v) y≤rad)
    {d : ℕ} {F : Frame G d} (S : SectionData F) (Y : Hol G) {μ : ℝ}
    (reader : Readable Y S (rp).p (R.family.side (j+1) per) μ) :
    let s := (Stock.census V).fire v
    let change := ε*g^((order:ℝ)+1-η)*P.cost
    WilsonCenteredFiledAtoms.Store rp S Y y κ
      (WilsonOlderFreshReversionStore.price (rp).p S Y Z rad μ allowance κ (Poly.toll P.w s) change (allFee*change))
      (fun U=>((rp).eval U:ℂ)*((Integral.markedLog g U upperBank).part s-(Spill.Foundry.uncut L.model gl x U).part s)) := by
  intro s change
  letI : Countable P.modelIndex:=P.modelCount
  letI students : Countable (Scene.Texts P.model
    (Pane.panel R.alloy (j+1) (R.alloy.B.a.S.oneStep (j+1) per).exact_size).ratio
    (Cruise.publish D R.rolls Q R.alloy φ books P.op (Oak.era R hk D Q π Γ hi P.op P.lesson)
      (R.alloy.B.a.S.oneStep (j+1) per).exact_size P.model order P.voter P.lesson.entry)) := Scene.crewC P.model
    (Pane.panel R.alloy (j+1) (R.alloy.B.a.S.oneStep (j+1) per).exact_size).ratio
    (Cruise.publish D R.rolls Q R.alloy φ books P.op (Oak.era R hk D Q π Γ hi P.op P.lesson)
      (R.alloy.B.a.S.oneStep (j+1) per).exact_size P.model order P.voter P.lesson.entry)
    (Cruise.funded D R.rolls Q R.alloy φ books P.op (Oak.era R hk D Q π Γ hi P.op P.lesson)
      (R.alloy.B.a.S.oneStep (j+1) per).exact_size P.model order P.voter P.lesson.entry P.lesson.studied ahead)
  have actual:=(course.1.walk (j+1) hi cut.le).truep
  obtain ⟨K⟩:=WilsonCenteredCourseKeeper.original R course (j+1) hi cut
  obtain ⟨div,pos,room⟩:=(eventually_atTop.mp (WilsonCenteredCaptureClock.original R simple)).choose_spec (j+1) late
  rw [←actual.point] at room
  have wage:=WilsonOlderFreshFiledWord.masked R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor
    physical P course cut pass month fits narrow hospital load simple positive unit ep opened
  have gross:=booked R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor
    physical P course cut pass month fits narrow simple positive unit ep opened
  have width : α=(rp).p.supportExponent+2 := by ring
  have low:=wage.1
  rw [width] at low gross
  obtain ⟨A,format,fee,field⟩:=@WilsonOlderFreshReversionStore.original G (R.family.side (j+1) per) V (Wallet actors) _ _ students
    rp roots (Stock.census V) d F reverted x s v (mem_singleton_self _) P.w
    P.issued.earning.positive change (allFee*change) low gross y Z center member rad near K _ _ _ _ allowance κ μ
    actual.valid div room pos S Y reader
  refine ⟨A,format,fee,fun U=>?_⟩
  have ticket:=WilsonOlderFreshFiledWord.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor
    physical P L file course cut x U
  have equal : WilsonRootedKioskOccupiedSlip.bare reverted x U =
      Integral.markedLog g U upperBank-Integral.markedLog (Coat.gStep (older).beta) U bankNow := ticket.2.2.2.tsum_eq
  refine (field U).trans (congrArg (fun z : ℂ=>((rp).eval U:ℂ)*z) ?_)
  exact (congrArg (fun z : Poly (Stock.census V)=>z.part s) equal).trans
    (congrArg (fun z : Poly (Stock.census V)=>(Integral.markedLog g U upperBank).part s-z.part s) ticket.2.1.symm)

end YM.Integration.WilsonOlderFreshFiledStep
