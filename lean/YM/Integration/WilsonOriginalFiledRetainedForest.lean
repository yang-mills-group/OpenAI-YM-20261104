import YM.Integration.WilsonOriginalReceivedProgram
import YM.Integration.WilsonOriginalRetainedForestFiling
/-! The same numerical second forest is booked on the actual lower Filed post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFiledRetainedForest
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

open Precision QuadraticLocal.Sunrise
local notation "C₀" => Stock.census V
local notation "level₀" => (Burn.horizon k+2)
local notation "tape₀" => AllOrder.Floe.Step.tape level₀
local notation "grade₀" => (fun s:Multi.Hot C₀=>Launch.index C₀ grades s.val+1)
local notation "receive₀" retained:max gauge:max =>
  WilsonOriginalCoverJetColors.colors (QuadraticLocal.Fk.money (π (j+1)) tape₀) grade₀ retained
    (WilsonOriginalCoverJetColors.reset retained gauge ((Rebirth.caliber (Γ (j+1)) origin).back level₀))
local notation "raw₀" div:max amount:max => copyColor div L.model grades (fun v=>(L.model v).paint amount) (π (j+1)) tape₀

def Reads (x:Wallet actors){grid:Side}(h:(R.family.side (j+1) per).val ∣ grid.val)
    (r:ℕ)(value:ℕ → Stationary.Link G grid → Poly C₀):Prop:=
  ∀{n:Side}{st:StepData n grid}{clip:Clip}{data:PathData G}{chart:ChartRatio G}
    (kernel:Bulk.Kernel st clip data chart)(forest:Forest st.ratio)(tag:st.Choices)(z:Exterior.fieldDir G n 1),
    Bulk.Fk kernel forest tag (raw₀ h x) z r = Bulk.Fk kernel forest tag (receive₀ r value) z r

include file in
theorem original (x:Wallet actors){grid:Side}(h:(R.family.side (j+1) per).val ∣ grid.val)
    (r:ℕ)(value:ℕ → Stationary.Link G grid → Poly C₀)
    (known:WilsonOriginalRetainedForestFiling.Reads R hk D Q π Γ books (floor.trans (Nat.le_succ j)) P.op P.lesson
      ahead actors P.model grades order P.voter x h r value):
    Reads R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P L x h r value:=by
  intro n st clip data chart kernel forest tag z
  have actual:=sameCopy L.model recorded file.passport file.names file.model x grades (π (j+1)) tape₀ h
  rw [actual]
  exact known kernel forest tag z

end YM.Integration.WilsonOriginalFiledRetainedForest
