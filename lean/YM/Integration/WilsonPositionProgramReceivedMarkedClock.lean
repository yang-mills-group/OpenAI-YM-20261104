import YM.Integration.WilsonOriginalReceivedFiniteChain
import YM.Integration.WilsonOriginalCoverJetColors
import YM.Integration.WilsonPositionProgramOccupiedClockBill
import YM.Integration.WilsonPositionProgramRelativeClock

/-! Transfer the complete signed occupied receipt of one filed Wilson post to the
chronological scalar chart. The source identity is required on the actual two adjacent posts. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramReceivedMarkedClock
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Stationary Comparison.RG02 Comparison.RG02.Order Further.PhysicalPeriodLimitF933 Laurent
open scoped Classical BigOperators

open WilsonOriginalReceivedChain
open Exterior FVA1Physical.Wilson Comparison.RG02.Assembly
open Comparison.RG02.Adjacent Comparison.RG02.Valence Comparison.RG02.Symmetry Comparison.RG02.Moving.Path

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


local notation "opK" => (RunFormalChain.fromRun R).step N (j+1) per cut
local notation "stencil" s:max => ∑ v∈(s).val.val, costAll (priorBank).power v

include file course cut pass month fits narrow in
theorem original (F : Forest (R.family.path.levels.clock.op (j+1) per).ratio)
    (tag : (R.family.path.levels.clock.op (j+1) per).Choices)
    (s : Multi.Hot (Stock.census V)) (T : UnitCost) (z : Stationary.Link G (R.family.side (j+1) per))
    (ticket : ℕ) (retained : ticket ≤ order) :
    let height := fun i : ℕ => i+2+(stencil s).toNat+(upperBank).power s
    let finite := fun t (a : Stationary.Link G (R.family.side (j+1) per)) =>
      Orbit.words opK F tag priorBank order s.val t (arm a)
    let deposited := fun t (a : Stationary.Link G (R.family.side (j+1) per)) =>
      (Air.discharge bankNow t (arm a)).part s.val
    ‖born finite T 0 order ticket z-
      born deposited (WilsonPositionProgramRelativeClock.relative back T) 0 order ticket z‖ ≤
      WilsonPositionProgramDatedClockBill.cost T 0 order ticket height
        (fun _ a => Oak.Tutoring.bill R hk D Q π Γ books hi P.op P.lesson ((a:ℝ) • z) P.cost /
          Poly.toll P.w s.val) := by
  let height := fun i : ℕ => i+2+(stencil s).toNat+(upperBank).power s
  let finite := fun t (a : Stationary.Link G (R.family.side (j+1) per)) =>
    Orbit.words opK F tag priorBank order s.val t (arm a)
  let deposited := fun t (a : Stationary.Link G (R.family.side (j+1) per)) =>
    (Air.discharge bankNow t (arm a)).part s.val
  let pupil := fun t (a : Stationary.Link G (R.family.side (j+1) per)) =>
    (Air.discharge upperBank t (arm a)).part s.val
  let grow := fun t : ℕ => ((height t):ℤ)
  have increasing : Monotone grow := by
    intro a b hab
    dsimp [grow,height]
    omega
  have legalHi : Legal tape₀ (π ((j+1)+1)) := by
    rw [P.lesson.ticket]
    exact AllOrder.Floe.Step.PlanV.audited R.rolls D _ _ _ P.lesson.entry
  have legalLo : Legal tape₀ (π (j+1)) := by
    rw [L.lesson.ticket]
    exact AllOrder.Floe.Step.PlanV.audited R.rolls D _ _ _ L.lesson.entry
  have incoming := Air.license P.model (fun a => (P.model a).paint x) grades P.w P.salary
    (Poetry.Agenda.stem ..) (fun a => P.salary.honor a x)
  have issued := Air.license stud (fun a => ((stud) a).paint x) grades P.w P.issued.earning
    (Poetry.Agenda.stem ..) (fun a => P.issued.earning.honor a x)
  have hw := (Air.standard P.model _ grades incoming (π ((j+1)+1)) tape₀ legalHi).1
  have hs := (Air.standard stud _ grades issued (π (j+1)) tape₀ legalLo).1
  have fine : Charge order grow finite := by
    intro t _
    have h := mark_read opK F tag priorBank (r:=order) _ s.val t (every _ _)
    have enlarged := h.promote (p:=((height t):ℤ)) (by dsimp [height]; omega)
    have att := SignCovariance.affine_degree (0 : fieldDir G (R.family.side (j+1) per) 1)
      (arm).toContinuousLinearMap enlarged
    simpa only [finite,grow,Orbit.words,Laplace.detail,zero_add,ContinuousLinearEquiv.coe_coe] using att
  have filed : Charge order grow pupil := by
    intro t _
    have h := WilsonOriginalCoverJetColors.occupied_degree upperBank hs.suppose_mark s t
    have att := SignCovariance.affine_degree (0 : fieldDir G (R.family.side (j+1) per) 1)
      (arm).toContinuousLinearMap h
    apply Level.promote (n:=(((upperBank).power s+t:ℕ):ℤ)) _ (by dsimp [grow,height]; omega)
    simpa only [zero_add,ContinuousLinearEquiv.coe_coe] using att
  have enter := WilsonOriginalReceivedChain.finite_step R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats floor physical P L file course cut pass month fits narrow x F tag
  have deposited_eq : ∀t ≤ order, deposited t=born pupil back 0 order t := by
    intro t ht
    funext a
    obtain ⟨_,_,_,paid⟩ := enter a t ht
    exact paid s.val
  have restored := WilsonPositionProgramRelativeClock.restored order pupil grow filed increasing back T ticket retained
  have same := WilsonPositionProgramRelativeClock.same_rows 0 order
    (WilsonPositionProgramRelativeClock.relative back T) deposited_eq ticket
  change ‖born finite T 0 order ticket z-born deposited _ 0 order ticket z‖ ≤ _
  rw [congrFun (same.trans restored) z]
  apply WilsonPositionProgramOccupiedClockBill.original T 0 order ticket height finite pupil fine filed z z
  intro t ht a _
  obtain ⟨err,agreement,paid,_⟩ := enter ((a:ℝ) • z) t ht
  have Pk := PhysicalWilsonPeriodizedMaterial.original R N (j+1) per cut (arm ((a:ℝ) • z))
    priorBank order F tag hw
  rw [← Pk] at agreement
  have face := congrArg (fun q : Poly (Stock.census V) => q.part s.val) agreement
  change finite t ((a:ℝ) • z)=pupil t ((a:ℝ) • z)+err.part s.val at face
  rw [face,add_sub_cancel_left]
  rw [le_div_iff₀ (Poly.worth P.issued.earning.positive s.val), mul_comm]
  exact (Poly.member P.issued.earning.positive s.val err).trans paid

end YM.Integration.WilsonPositionProgramReceivedMarkedClock
end
