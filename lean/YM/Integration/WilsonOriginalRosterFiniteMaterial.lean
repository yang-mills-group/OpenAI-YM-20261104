import YM.QuadraticLocal.Fk.Tutor
import YM.Integration.PhysicalWilsonPeriodizedMaterial

/-! The complete entered roster, including its deposited marks, on the original finite Wilson material. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalRosterFiniteMaterial
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

include course incoming
theorem original (outcost : ℝ)
    (outgoing : Scene.Armada M₁ w grades (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i))
      outcost order op.count shelf)
    (small : cost ≤ 1) :
    (∀ g, g ≠ 0 → ∀ U, HasSum (fun j => Poly.send (M j).mode ((M j).nominal g x U))
      (Integral.markedLog g U X₀)) ∧
    (∀ g, g ≠ 0 → ∀ U, HasSum (fun j => Poly.send ((M₁) j).mode (((M₁) j).nominal g x U))
      (Integral.markedLog g U X₁)) ∧
    ∀ j, j ≤ order → ∃ e : Poly marks,
      Order.observe marks order (Order.logMarked (PhysicalWilsonPeriodizedMaterial.reference R N i per cut b X₀ order)) j =
        Air.discharge X₁ j b + e ∧ Poly.price w e ≤ total ∧ HasSum (miss j) e ∧
        RG.SumBudget (fun c => Poly.price w ((miss j) c)) total := by
  obtain ⟨calendar⟩ := Oak.agrees R hk D Q π Γ Ψ course hi cut lesson
  have legal : Legal T₀ (π (i+1)) := by
    rw [lesson.ticket]
    exact AllOrder.Floe.Step.PlanV.audited R.rolls D _ _ _ lesson.entry
  have enter := Poetry.Agenda.stem D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
  have h₀ := Air.license M (fun a => (M a).paint x) grades w incoming enter (fun a => incoming.honor a x)
  have h₁ := Air.license M₁ (fun a => ((M₁) a).paint x) grades w outgoing (Poetry.Agenda.stem ..)
    (fun a => outgoing.honor a x)
  refine ⟨fun g hg U => Air.liftPassport M _ grades h₀ (π (i+1)) T₀ g hg U,
    fun g hg U => Air.liftPassport M₁ _ grades h₁ (π i) T₀ g hg U, ?_⟩
  intro j hj
  -- Apply the component estimates from `YM.QuadraticLocal.Fk.Tutor` directly
  -- to the given actor spaces and index type.
  have sale (z:Club M) : ‖ScatterR.history M (π (i+1)) T₀ K₀ F tag b z j order - Alliance.seen M
      (R.family.path.levels.clock.op i per).ratio A published j z‖ ≤ Oak.Tutoring.duty R hk D Q π Γ books hi lesson A := by
    have bigger : Bid.Larger (G:=G) (R.family.path.levels.clock.op i per) := calendar.clock.laws.data.room.larger
    have north : (R.family.path.rep N per (i+1)).path = lesson.entry.self.north :=
      ((RunFormalChain.fromRun R).selected N per (i+1) cut).trans lesson.studied.books.north.symm
    have cl : (R.family.path.rep N per (i+1)).clip = (R.metals.p.profile (R.alloy.B.a.clock.J (i+1))).clip :=
      ((RunFormalChain.fromRun R).clips N per (i+1) cut).trans (congrArg RG.Stage.clip (PriceCompiler.params_eq R.alloy.B.valid _))
    exact Cruise.unit_gate D R.rolls Q R.alloy φ books op (Oak.era R hk D Q π Γ hi op lesson) (R.alloy.B.a.S.oneStep i per).exact_size M z order voter lesson.entry (R.family.path.rep N per (i+1)).clip (R.family.path.rep N per (i+1)).path (π (i+1)) K₀ F tag lesson.ticket north cl bigger hj A
  obtain ⟨e,h,hp,hs⟩ := Guild.communion M grades w (R.family.path.levels.clock.op i per)
    published incoming (Poetry.Agenda.stem ..) K₀ F tag A (π (i+1)) (π i) T₀
    (Cruise.funded D R.rolls Q R.alloy φ books op (Oak.era R hk D Q π Γ hi op lesson) (R.alloy.B.a.S.oneStep i per).exact_size M order voter lesson.entry lesson.studied ahead)
    outcost outgoing x sale small (Poetry.Agenda.stem ..) (Poetry.Agenda.belt_p ..) (Oak.Tutoring.plus_nonneg ..) hj
  refine ⟨e, ?_, hp, hs, ?_⟩
  · have hw := (Air.standard M _ grades h₀ (π (i+1)) T₀ legal).1
    rw [← PhysicalWilsonPeriodizedMaterial.original R N i per cut b X₀ order F tag hw]
    exact h
  · exact Alliance.receipt M _ grades w incoming enter _ small (Oak.Tutoring.plus_nonneg R hk D Q π Γ books hi lesson A)
      K₀ F tag A (π (i+1)) T₀ published (fun a => incoming.honor a x)
      sale

end YM.Integration.WilsonOriginalRosterFiniteMaterial
end

