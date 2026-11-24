import YM.Integration.WilsonMeasuredOwnerReserve

/-! Integrability before either of the physical flat measurements. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnerIntegrable
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open Tree AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV QuadraticLocal.Advent
open Push Push.Local Push.PriceCompiler AnalyticBridge VerifiedReset RemainderComparison
open AllOrder.Transit WheelP PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Pressure ConnectedActivityE6 Filter
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N per m k b:ℕ} (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
    (Ψ:∀j,RG.Rep G (R.family.side j per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (begun:m ≤ b) (live:b ≤ N) {d:ℕ} {F:Frame G d} (S:SectionData F)
    (A:Hol G) (y:Site (R.family.side b per)) (q:Coefficient F (R.family.side b per))
    (law:q.Format y A (Ψ b)) {κ M:ℝ} (income:q.remBound y (Ψ b) κ M)

include course begun live S A y law income in
theorem original : Integrable (account q (Ψ b)) (prior G _) := by
  have valid:=(course.1.walk b begun live).truep.valid
  have ⟨formed,paid,split,_⟩:=WilsonMeasuredOnlyHard.original q (Ψ b) (Ψ b) rfl rfl rfl S A y κ M law income
  have correction:account q (Ψ b)=(fun U=>q.density y S (Ψ b) U-(soft q).density y S (Ψ b) U) := by
    funext U
    rw [split,add_sub_cancel_left]
  rw [correction]
  exact ((q.envelope S valid income law).integrableC _).sub
    (((soft q).envelope S valid paid formed).integrableC _)

include course begun live S A y law income in
theorem pair : Integrable (account q (Ψ b)) (prior G _) ∧
    Integrable (q.density y S (Ψ b)) (prior G _) := by
  exact ⟨original R π Γ Ψ course begun live S A y q law income,
    (q.envelope S (course.1.walk b begun live).truep.valid income law).integrableC _⟩

end YM.Integration.WilsonMeasuredOwnerIntegrable
