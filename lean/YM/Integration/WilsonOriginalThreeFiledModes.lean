import YM.Integration.WilsonOriginalReceivedCopiedCover
import YM.Integration.WilsonOriginalCoverNominalPairSource
import YM.Integration.WilsonOriginalCoverNominalThirdSource

/-! Pair and third conditional coefficients on one actual occupied three-name course. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalThreeFiledModes
open FVA1Physical.TwoReset
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
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {X : Fin 3 → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : Fin 3 → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census (Fin 3)))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)


local notation "tape" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "cash" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter

local notation "modes" => WilsonSeparatedOriginalJointLog.three
local notation "pair" => WilsonOriginalCoverNominalPairSource.Filed
local notation "third" => WilsonOriginalCoverNominalThirdSource.Filed
local notation "copies" => WilsonOriginalCopiedHistory.Values G modes (R.family.side i per)

def Read (named : Wallet actors → copies) : Prop :=
  (∀ (a d : Fin 3) (s : (modes).Mode), a ≠ d → s.val = {a,d} →
    pair R cut (π (i+1)) tape order P.model grades named a d s) ∧
  third R cut (π (i+1)) tape order P.model grades named

include course in
theorem original (named : Wallet actors → copies)
    (issued : ∀ (x : Wallet actors) (grid : Side) (multiple : (R.family.side i per).val ∣ grid.val)
      (j : ℕ), j ≤ order → ∀ y, named x grid multiple j y = peek multiple student grades (π (i+1)) tape x j y) :
    Read R hk D Q π Γ Ψ books hi cut ahead actors pieces grades order shelf seats physical P named := by
  have valid : Legal tape (π (i+1)) := by
    rw [P.lesson.ticket]
    exact AllOrder.Floe.Step.PlanV.audited R.rolls D _ _ _ P.lesson.entry
  have funded : ∀ x : Wallet actors, ∃ (fee:ℝ) (cap:ℕ),
      Air.Staff P.model (fun v=>(P.model v).paint x) grades fee cap := by
    intro x
    exact ⟨_,_,Air.license P.model _ grades P.w P.salary (Poetry.Agenda.stem ..)
      (fun v=>P.salary.honor v x)⟩
  have represented := WilsonOriginalReceivedCopiedCover.published (R:=R) (P:=P) (course:=course) (cut:=cut)
  refine ⟨?_, ?_⟩
  · intro a d s apart both
    apply WilsonOriginalCoverNominalPairSource.received R cut (π (i+1)) tape order P.model grades student
      named a d s _ issued
    exact WilsonOriginalCoverNominalTable.received R cut (π (i+1)) tape order P.model grades student
      a d s apart both represented funded valid
  · apply WilsonOriginalCoverNominalThirdSource.received R cut (π (i+1)) tape order P.model grades student
      named _ issued
    exact WilsonOriginalCoverNominalThirdTable.received R cut (π (i+1)) tape order P.model grades student
      represented funded valid

end Measured
end YM.Integration.WilsonOriginalThreeFiledModes
