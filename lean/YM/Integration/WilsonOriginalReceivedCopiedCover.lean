import YM.Integration.WilsonOriginalReceivedPost
import YM.Integration.FVA1Physical.TwoReset.ActualCover

/-! Copied finite Wilson contractions for the earned post on its original history. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalReceivedCopiedCover
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


local notation "tape" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "cash" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter

include course in
theorem published : FVA1Physical.TwoReset.RepresentsCover R cut (π (i+1)) tape order P.model grades student := by
  obtain ⟨stage, _, _⟩ := (course.2 i hi cut).earns
  have room := stage.laws.data.room.larger
  let epoch := Oak.era R hk D Q π Γ hi P.op P.lesson
  let press := Cruise.funded D R.rolls Q R.alloy φ books P.op epoch
    (R.alloy.B.a.S.oneStep i per).exact_size P.model order P.voter P.lesson.entry P.lesson.studied ahead
  exact FVA1Physical.TwoReset.exact_mark_binding R D Q books cut P.op epoch P.lesson.entry
    P.lesson.studied room P.model grades order P.voter press cash (π (i+1)) P.lesson.ticket P.salary
    (Poetry.Agenda.stem ..) (P.affordable.trans (inv_le_one_of_one_le₀ P.issued.Waffle.cool))
    (fun t => Air.license student _ grades P.w P.issued.earning (Poetry.Agenda.stem ..)
      (fun z => P.issued.earning.honor z t))

end Measured
end YM.Integration.WilsonOriginalReceivedCopiedCover
