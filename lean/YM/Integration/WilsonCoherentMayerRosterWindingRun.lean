import YM.Integration.WilsonOriginalRosterFiniteMaterial
import YM.Integration.WilsonCoherentMayerWindingTemperature

/-! The evaluated original course on its full marked roster at the inherited temperature. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerRosterWindingRun
open Filter
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (hi : m ≤ i) (cut : i < N)
  (op : Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson : Lesson (N:=N) R hk D Q π Γ hi)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V ι : Type} [Fintype V] [DecidableEq V] {marks : Census V} {X : V → Type}
  {passport : Earn.Passport (R.family.side (i+1) per) V}
  (actors : ∀ v, Set (X v)) (M : ι → Row passport marks G (Affinity.Wallet actors))
  (w : V → ℝ) (grades : V → ℕ) (order shelf : ℕ)
  (voter : Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
    order op.count op.stage k (R.alloy.B.a.clock.J i))
  (cost : ℝ)
  (incoming : Scene.Armada M w grades (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
    cost order op.count shelf)
  (x : Affinity.Wallet actors)
  (F : Forest (R.family.path.levels.clock.op i per).ratio) (tag : (R.family.path.levels.clock.op i per).Choices)
  (A : Stationary.Link G (R.family.side i per))

local notation "T₀" => AllOrder.Floe.Step.tape (Burn.horizon k + 2)
local notation "X₀" => Air.craft M (fun j => (M j).paint x) grades (π (i+1)) T₀
local notation "M₁" => Oak.student (n:=per) R hk D Q π Γ books hi op lesson ahead actors M order voter
local notation "X₁" => Air.craft M₁ (fun j => ((M₁) j).paint x) grades (π i) T₀
local notation "b" => Stationary.arm G (R.family.side i per) 1 A
local notation "K₀" => (RunFormalChain.fromRun R).step N i per cut
local notation "published" => Mentor.Cruise.publish D R.rolls Q R.alloy φ books op
  (Oak.era R hk D Q π Γ hi op lesson) (R.alloy.B.a.S.oneStep i per).exact_size M order voter lesson.entry
local notation "miss" r:max => Alliance.miss M (fun j => (M j).paint x) (R.family.path.levels.clock.op i per).ratio
  K₀ F tag A (π (i+1)) T₀ published r
local notation "total" => Oak.Tutoring.bill R hk D Q π Γ books hi op lesson A cost

open ConnectedActivityE6
noncomputable def firstDate {G:Gauge}(R:Run G)(simple:G.Simple):ℕ:=
  (eventually_atTop.mp (WilsonCoherentMayerWindingTemperature.purchased R simple)).choose

local notation "g" => ((Coat.gStep (R.family.path.rep N per (i+1)).beta):ℂ)
local notation "point" => Order.value g (Order.logMarked (PhysicalWilsonPeriodizedMaterial.reference R N i per cut b X₀ order))
local notation "folded" => WilsonCoherentMayerWindingGrades.panel order g (fun j=>Air.discharge X₁ j b)
local notation "delta₁" => fun c=>WilsonCoherentMayerWindingGrades.panel order g (fun j=>(miss j) c)

include course incoming in
theorem original (outcost:ℝ)
    (outgoing:Scene.Armada M₁ w grades (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i))
      outcost order op.count shelf)
    (small:cost≤1) (simple:G.Simple) (opened:firstDate R simple ≤ i+1):
    (∀ h, h ≠ 0 → ∀ U, HasSum (fun j=>Poly.send (M j).mode ((M j).nominal h x U))
      (Integral.markedLog h U X₀)) ∧
    (∀ h, h ≠ 0 → ∀ U, HasSum (fun j=>Poly.send ((M₁) j).mode (((M₁) j).nominal h x U))
      (Integral.markedLog h U X₁)) ∧
    HasSum delta₁ (point-folded) ∧
      RG.SumBudget (fun c=>Poly.price w (delta₁ c)) (2*total) ∧
      Poly.price w (folded-point) ≤ 2*total:=by
  have issued:=WilsonOriginalRosterFiniteMaterial.original R hk D Q π Γ Ψ course books hi cut op lesson ahead
    actors M w grades order shelf voter cost incoming x F tag A outcost outgoing small
  have budget:=WilsonCoherentMayerWindingGrades.evaluated w incoming.positive order g
     (Order.logMarked (PhysicalWilsonPeriodizedMaterial.reference R N i per cut b X₀ order))
     (fun j=>Air.discharge X₁ j b) (fun j=>miss j) (fun _=>total) issued.2.2
  have late:= (eventually_atTop.mp (WilsonCoherentMayerWindingTemperature.purchased R simple)).choose_spec
  have temp:‖g‖≤1/2:=late (i+1) opened N per cut
  have price:0≤total:=by
    obtain ⟨e,_,h,_⟩:=issued.2.2 0 (Nat.zero_le _)
    exact (Poly.nonnegative incoming.positive e).trans h
  have tariff:=WilsonCoherentMayerWindingGrades.capped g temp order total price
  exact ⟨issued.1,issued.2.1,budget.1,Push.AbsoluteSums.budget_loosen budget.2.1 tariff,budget.2.2.trans tariff⟩

end YM.Integration.WilsonCoherentMayerRosterWindingRun
