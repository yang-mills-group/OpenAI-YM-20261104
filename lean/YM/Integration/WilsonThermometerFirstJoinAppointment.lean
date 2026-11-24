import YM.Integration.WilsonThermometerFirstJoinReturn
import YM.Integration.WilsonOriginalReceivedCountedChain

/-! Keep the genuine enrollment and all filed physical test radii from one measured semester. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerFirstJoinAppointment
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity QuadraticLocal.Tint Pressure ConnectedActivityE6
open WilsonOriginalReceivedChain WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open FVA1 Finset Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter OriginalForcedAddresses
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonThermometerCourseIntake
open scoped Classical BigOperators Topology

open WilsonThermometerCourseHearing WilsonPositionThermometerGradedReading LocalComparison ActualPolynomialContraction MergeProof.Accent


variable {G : Gauge} (R : Run G) {m j N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  (order shelf seats : ℕ) (floor : m ≤ j) (A : Group R.family 6)
  (simple : G.Simple) (cut : j+1<N) (o : Positions (Fin 3) (R.family.side N per))
local notation "actors" => disks
local notation "pieces" => sectors
local notation "grades" => (fun z : Fin 3 => (grade z).val)

variable (P : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1)
    (floor.trans (Nat.le_succ j)) (offered R A simple cut o))

local notation "earlier" => (fun x : Wallet actors => LocalComparison.actualPush R.family N per (j+1) ((offered R A simple cut o) x))
local notation "elected" => Oak.expenseReal R hk D Q π Γ books (floor.trans (Nat.le_succ j)) P.op P.lesson ahead order shelf
local notation "hi" => floor.trans (Nat.le_succ j)
variable [Countable P.inputIndex]
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  (scroll:VowsR.LawScroll G φ) (chamber:VowsR.Chamber scroll R.kit D Q books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  (load:P.op.count≤Burn.horizon k+2) (wide:shelf≤R.alloy.B.a.clock.J (j+1)) (test:Wallet actors)
local notation "initial" op:max => op R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1)
  (floor.trans (Nat.le_succ j)) (offered R A simple cut o) P simple cut course scroll chamber hospital load wide test
local notation "issued" => initial WilsonOriginalReceivedFirstEnrollment.installed
local notation "afterPost" => WilsonOriginalReceivedChain.Post (N:=N) (V:=Fin 3) (X:=fun _ => ℂ)
  R hk D Q π Γ Ψ books ahead disks sectors (fun z : Fin 3 => (grade z).val) order shelf seats j floor
  (fun x : Wallet disks => LocalComparison.actualPush R.family N per (j+1) (offered R A simple cut o x))
local notation "history" L:max => WilsonOriginalReceivedChain.Filed R hk D Q π Γ Ψ books ahead disks sectors
  (fun z : Fin 3 => (grade z).val) order shelf seats floor (offered R A simple cut o) (issued) L
local notation "gf" => Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta

structure Record (q : ℕ) (ε h C E τ : ℝ) where
  post : afterPost
  counted : Countable post.inputIndex
  formalBudget : C ≤ Advent.budgetR R (j+1)
  oldBudget : E ≤ P.rent+ε*gf^q
  capital : post.cost=h⁻¹*C
  salary : post.rent=max (h⁻¹*E) τ
  weights : ∀ a : Fin 3, post.w a=P.w a/(elected^6*h)
  full : 1 ≤ h
  budget : h ≤ max 1 (max (Advent.budgetR R j*Advent.budgetR R (j+1)) (P.rent+ε*gf^q))
  filed : history post

local notation "invoice" q:max ε:max h:max cc:max ee:max τ:max => Record R hk D Q π Γ Ψ books ahead order shelf seats floor
  A simple cut o P course scroll chamber hospital load wide test q ε h cc ee τ

theorem original (path : PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ)
    (pass : AllOrder.Transit.Pass D Q R.alloy R.kit) (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (fits : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J j)
    (seated : seats ≤ Burn.horizon k+2) (packed : order+shelf ≤ Burn.horizon k+2)
    (q : ℕ) (deep : 2*q+8 ≤ order) (aged : q+3 ≤ 3*k+2) {ε : ℝ} (ep : 0 < ε)
    (late : WilsonReceivedMeasuredStampPrice.opening R simple q order k deep aged ep ≤ j+1) :
    ∃ h C E : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ 1 → Nonempty (invoice q ε h C E τ) := by
  have grant := WilsonOriginalReceivedChain.next_filed_counted R hk D Q π Γ Ψ books ahead
    disks sectors (fun z : Fin 3 => (grade z).val) order shelf seats floor (offered R A simple cut o)
    (issued) course path cut pass scroll chamber month hospital fits narrow seated packed simple q deep aged ep late test
  obtain ⟨h,C,E,lesson₂,full,costBound,oldBound,all⟩ := grant
  refine ⟨h,C,E,fun τ active safe => ?_⟩
  obtain ⟨L,_,weights,capital,salary,_,budget,filed,counted⟩ := all τ active safe
  exact ⟨⟨L,counted,costBound,oldBound,capital,salary,weights,full,budget,filed⟩⟩

end YM.Integration.WilsonThermometerFirstJoinAppointment
end
