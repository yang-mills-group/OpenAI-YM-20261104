import YM.Integration.WilsonReceivedSingletonMass
import YM.QuadraticLocal.Fk.Tutor

/-! The two ordinary singleton factors in the physical capture are charged to
the actual student's finite-order colored rows and its native winding bill. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedFiniteSingleton
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open scoped Classical BigOperators Topology

section Measured
variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)
  (x : Wallet actors) (A : Stationary.Link G (R.family.side i per))

local notation "gf" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "sheet" => R.family.path.levels.clock.op i per
local notation "angle" => Stationary.arm G (R.family.side i per) 1 A

local notation "T₀" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "X₀" => Air.craft P.model (fun j => (P.model j).paint x) grades (π (i+1)) T₀
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors P.model order P.voter
local notation "X₁" => Air.craft student (fun j => (student j).paint x) grades (π i) T₀
local notation "seam" => Oak.Tutoring.bill R hk D Q π Γ books hi P.op P.lesson A P.cost

local notation "program" => (RunFormalChain.fromRun R).step N i per cut
local notation "J" => (Stock.census V)
local notation "κ" a:max => Poly.toll P.w ((J).fire a)

include course in
theorem original (F : Forest (sheet).ratio) (tag : (sheet).Choices) (a : V) :
    let W := Bulk.Fk program F tag X₀ angle order
    let p := WilsonIndependentOrdinaryPairGrade.slot ((J).fire a) (Order.render (Order.ratio W))
    let invoice := ∑ j∈range (order+1), (κ a * ‖(Air.discharge X₁ j angle).part ((J).fire a)‖ + seam)
    κ a * WilsonIndependentOrdinaryPairGrade.mass p ≤ invoice ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 → κ a * ‖(Order.value z (Order.logMarked W)).part ((J).fire a)‖ ≤ invoice := by
  intro W p invoice
  letI : Countable P.modelIndex := P.modelCount
  obtain ⟨calendar⟩ := Oak.agrees R hk D Q π Γ Ψ course hi cut P.lesson
  have unit : Order.UnitLeading W := Assembly.prescription_unit ..
  have sym : Order.Symmetric W := Assembly.prescription_sym (hv := (program).positive F tag) ..
  have positive := (Poly.worth P.issued.earning.positive ((J).fire a)).le
  have small : P.cost ≤ 1 := P.affordable.trans (inv_le_one_of_one_le₀ P.issued.Waffle.cool)
  have price : κ a * WilsonIndependentOrdinaryPairGrade.mass p ≤ invoice := by
    apply WilsonReceivedSingletonMass.issued W unit sym a (κ a)
      (fun j => κ a * ‖(Air.discharge X₁ j angle).part ((J).fire a)‖)
      (fun _ => seam) (fun j => Air.discharge X₁ j angle) positive
    · intro j hj
      obtain ⟨e,eqn,bound,_⟩ := Oak.Tutoring.fund R hk D Q π Γ Ψ books hi cut P.op P.lesson calendar ahead
        actors P.model P.w grades order shelf P.voter P.cost P.salary x F tag j A hj small _ P.issued.earning
      exact ⟨e,eqn,(Poly.member P.issued.earning.positive ((J).fire a) e).trans bound⟩
    · exact fun _ _ => le_rfl
  exact ⟨price, fun z smallZ => (mul_le_mul_of_nonneg_left
    (WilsonReceivedSingletonMass.measured W unit sym a z smallZ) positive).trans price⟩

end Measured
end YM.Integration.WilsonReceivedFiniteSingleton
