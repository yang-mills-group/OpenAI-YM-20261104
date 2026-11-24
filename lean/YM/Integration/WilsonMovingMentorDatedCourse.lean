import YM.Integration.WilsonMovingMentorTerrace
import YM.Integration.WilsonMovingMentorConcourseRows

/-! The high marked course and all its true density and regular activity
receipts are selected on one physical assignment before the period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorDatedCourse
open Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Org Push.PriceCompiler AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Transit AllOrder.Transit.WheelP
open scoped Classical

variable {G : Gauge} (R : Run G)

theorem original (simple : G.Simple) (bought : WilsonMovingMentorWarm.Conditions R.kit)
    {r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
    {Q : r.Tab R.rolls} (funded : Pass r Q R.alloy R.kit)
    (q k : ℕ) (grade : q ≤ 3*k+2) {ε : ℝ} (positive : 0 < ε) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ N, m ≤ N →
      ∃ π Γ, PlanV.Path r R.alloy Q (Burn.horizon k) N m π Γ ∧ ∀ per : ℕ,
        ∃ H : (i : ℕ) → RG.Rep G (R.alloy.B.a.S.side i per),
          Concourse R.alloy R.kit R.T π Γ m N per k H ∧
          Topline (H N) (R.alloy.B.a.clock.forcedAllowance N) ∧
          ∀ i, m ≤ i → i ≤ N →
            (H i).beta = (R.family.path.rep N per i).beta ∧ (H i).eval = (R.family.path.rep N per i).eval ∧
            ∃ C : Burn.Seed (H i) (M0 k 0 (R.alloy.B.a.budget i) (π i) (R.family.path.rep N per i).beta),
              Burn.Candor (R.alloy.B.a.budget i) (H i).activities (Set.range C.model)
                (Burn.silver (R.alloy.B.a.clock.hatBeta i)) (ε * (Pert.Asymptotics.regulatorRun R.family N per i)^q) := by
  filter_upwards [R.family.path.levels.fits.deep.eventually_ge_atTop (Burn.horizon k+2),
    WilsonMovingMentorConcourseRows.original R simple q k grade positive] with m height track N live
  obtain ⟨π,Γ,route,byPeriod⟩ := WilsonMovingMentorTerrace.original R simple bought funded height live
  refine ⟨π,Γ,route,?_⟩
  intro per
  obtain ⟨H,history,top,actual⟩ := byPeriod per
  refine ⟨H,history,top,fun i before after => ?_⟩
  exact ⟨(actual i before after).1,(actual i before after).2.1,track N per π Γ H history i before after⟩

end YM.Integration.WilsonMovingMentorDatedCourse
end
